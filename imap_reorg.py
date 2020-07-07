#! /usr/bin/env python3
"""
Synopsis: reorganize imap mailboxes

Usage: %(appname)s [-hVvfs][-l log][-u user][-p pw]
                  [user[:password@]]imapserver[:port] expr..
       -h, --help           this message
       -V, --version        print version and exit
       -v, --verbose        verbose mode (cumulative)
       -l, --logfile=fname  log to this file
       -f, --force          force operation (unused)
       -s, --ssl            disable SSL
       -u, --user=id        user id
       -p, --password=pw    user password

Notes:

Check mailbox delimiter with folder command.
If user contains an ':' or password an '@', specify user and/or password
separately.

Expressions:
folder[:mailbox]            list mailbox folders
yearly:year:mailbox:dest    select mails with internal date in year from
                            mailbox and move to dest

Examples:
yearly:2017:INBOX:INBOX.2017
move all messages with internal date in 2017 to INBOX.2017

yearly:2019:INBOX.listen.linux.kernel:INBOX.listen.linux.kernel.2019
move all kernel meesages of 2019 in subfolder

Todo:
Create missing folders recursively

Copyright:
(c)2020 by %(author)s

License:
%(license)s
"""
#
# vim:set et ts=8 sw=4:
#

__version__ = '0.2'
__author__ = 'Hans-Peter Jansen <hpj@urpla.net>'
__license__ = 'GNU GPL v2 - see http://www.gnu.org/licenses/gpl2.txt for details'


import os
import sys
import time
import email
import email.utils
import getopt
import imaplib
import imap_tools
import logging
import logging.handlers
import datetime
import functools

# raise readline limit to 16M
imaplib._MAXLINE = 16 * 1024 * 1024

class gpar:
    """Global parameter class"""
    appdir, appname = os.path.split(sys.argv[0])
    if appdir == '.':
        appdir = os.getcwd()
    if appname.endswith('.py'):
        appname = appname[:-3]
    version = __version__
    author = __author__
    license = __license__
    loglevel = logging.ERROR
    logfile = None
    force = False
    ssl = True

    # internal
    user = None
    password = None
    server = None
    port = None
    expr = []
    imap = None
    limit = 10000   # copy/move this number of messages at once


log = logging.getLogger(gpar.appname)

stdout = lambda *msg: print(*msg, file = sys.stdout, flush = True)
stderr = lambda *msg: print(*msg, file = sys.stderr, flush = True)

# return codes (or-able)
NOERR, ERRARGS, ERRLOGIN, ERREXPR, ERREXPRARGS, ERRPROT, ERRUNDEF = 0, *(1 << i for i in range(6))

errdict = {
    NOERR: 'No error',
    ERRARGS: 'Argument error',
    ERRLOGIN: 'Login error',
    ERREXPR: 'Expression error',
    ERREXPRARGS: 'Error in expression arguments',
    ERRPROT: 'Protocol error',
    ERRUNDEF: 'Undefined error',
}


class trace:
    """Trace decorator class"""
    def __init__(self, loglevel = logging.DEBUG, maxlen = 20):
        self.loglevel = loglevel
        self.maxlen = maxlen

    def abbrev(self, arg):
        if arg:
            argstr = repr(arg)
            if len(argstr) > self.maxlen:
                argstr = argstr[:self.maxlen] + "..'"
            return argstr
        return arg

    def argstr(self, *args, **kwargs):
        arglist = []
        for arg in args:
            if arg:
                arglist.append(self.abbrev(arg))
        for k, v in kwargs.items():
            arglist.append('{} = {}'.format(k, self.abbrev(v)))
        return ', '.join(arglist)


    def __call__(self, func):
        @functools.wraps(func)
        def trace_and_call(*args, **kwargs):
            result = func(*args, **kwargs)
            argstr = self.argstr(*args, **kwargs)
            logging.log(self.loglevel, '{}({}): {}'.format(func.__name__, argstr, result))
            return result
        return trace_and_call


def exit(ret = 0, msg = None, usage = False):
    """Terminate process with optional message and usage"""
    if msg:
        stderr('%s: %s' % (gpar.appname, msg))
    if usage:
        stderr(__doc__ % gpar.__dict__)
    sys.exit(ret)


def setup_logging(logfile, loglevel):
    """Setup various aspects of logging facility"""
    logconfig = dict(
        level = loglevel,
        format = '%(asctime)s %(levelname)5s: [%(name)s] %(message)s',
        datefmt = '%Y-%m-%d %H:%M:%S',
    )
    if logfile not in (None, '-'):
        logconfig['filename'] = logfile
    logging.basicConfig(**logconfig)


def fsize(value, suffix = 'B'):
    ''' format a size value in human readable form '''
    for unit in ('','K','M','G','T','P','E','Z'):
        if abs(value) < 1024.0:
            return '%3.1f %s%s' % (value, unit, suffix)
        value /= 1024.0
    return '%.1f %s%s' % (value, 'Y', suffix)


def fdeltat(td, short = False, fuzzy = False):
    ''' return a human readable representation of timedelta, int or float values
        int or float values are expected to be the number of seconds already
        if fuzzy is true, just return the first value
    '''
    rv = []
    if isinstance(td, datetime.timedelta):
        td = td.total_seconds()
    hours, minutes = 0, 0
    secs, fraction = divmod(td, 1)
    secs = int(secs)
    if secs >= 60:
        # ignore fractional part, if dt is >= 1 min
        fraction = 0
    else:
        # convert to msecs
        fraction *= 1000

    for singular, plural, period in (
        ('year',    'years',    60 * 60 * 24 * 365),
        ('month',   'months',   60 * 60 * 24 * 30),
        ('week',    'weeks',    60 * 60 * 24 * 7),
        ('day',     'days',     60 * 60 * 24),
        ('hour',    'hours',    60 * 60),
        ('minute',  'minutes',  60),
        ('second',  'seconds',  1),
    ):
        if secs > period or period == 1:
            val, secs = divmod(secs, period)
            if short:
                if period > 60 * 60:
                    rv.append('%s%s' % (val, singular[0]))
                elif period == 60 * 60:
                    hours = val
                elif period == 60:
                    minutes = val
                elif period == 1:
                    if fraction:
                        val = '%d.%03d' % (val, fraction)
                    else:
                        val = '%02d' % (val)
            else:
                if period == 1 and fraction:
                    val = '%d.%03d' % (val, fraction)
                if val == 1:
                    rv.append('%s %s' % (val, singular))
                else:
                    rv.append('%s %s' % (val, plural))
                if fuzzy:
                    break

    if short:
        return ''.join(rv) + '%02d:%02d:%s' % (hours, minutes, val)
    else:
        # in 1 hour, 33 minutes, 12 seconds
        # -> 1 hour, 33 minutes and 12 seconds
        return ' and '.join(', '.join(rv).rsplit(', ', 1))


class ImapReorgError(Exception):
    def __init__(self, errcode, errmsg = None):
        if errcode not in errdict:
            errcode = ERRUNDEF
        self.errcode = errcode
        self.errmsg = errmsg

    def __str__(self):
        if self.errmsg:
            return '%s: %s' % (errdict[self.errcode], self.errmsg)
        else:
            return '%s' % (errdict[self.errcode])


class ImapReorg:
    def __init__(self, user, password, server, port = None, ssl = True, limit = None):
        self._user = user
        self._password = password
        self._server = server
        self._ssl = ssl
        if not port:
            if self._ssl:
                port = 993
            else:
                port = 143
        self._port = port
        self._limit = limit
        self._imap = self._connect(user, password, server, port, ssl)
        log.info('login successful: %s@%s:%s', user, server, port)

    def _connect(self, user, password, server, port, ssl):
        try:
            if ssl:
                imap = imap_tools.MailBox(server, port)
            else:
                imap = imap_tools.MailBoxUnencrypted(server, port)
            imap.login(user, password)
        except imaplib.IMAP4.error as e:
            raise ImapReorgError(ERRLOGIN, e)
        return imap

    def _run_expr(self, expr):
        func, *args = expr.split(':')
        if func.startswith('_'):
            raise ImapReorgError(ERREXPR, 'invalid function <%s>' % func)

        try:
            method = getattr(self, func)
        except AttributeError as e:
            raise ImapReorgError(ERREXPR, 'invalid function <%s>' % func)

        try:
            return method(*args)
        except TypeError as e:
            raise ImapReorgError(ERREXPR, 'invalid arguments for <%s: %s>' % (func, args))

    def _select(self, mailbox):
        try:
            resp, data = self._imap.folder.set(mailbox)
        except imap_tools.utils.UnexpectedCommandStatusError as e:
            log.debug('select: %s', e)
            return False, 0
        if resp == 'OK':
            return True, int(data[0].decode('utf-8'))
        return False, 0

    def _create(self, mailbox):
        ret = self._imap.folder.create(mailbox)
        if ret[0] == 'OK':
            log.debug('create: %s', ret)
            return True
        log.error('create: failed: %s', ret)
        return False

    def _list(self, mailbox):
        for folder in self._imap.folder.list(mailbox):
            yield folder['name']

    def _logout(self):
        try:
           ret = self._imap.logout()
        except imaplib.IMAP4.error as e:
            raise ImapReorgError(ERRPROT, e)
        return NOERR

    def folder(self, mailbox = ''):
        log.info('list(mailbox: %s)', mailbox)
        for mailbox in self._list(mailbox):
            log.info(mailbox)
        return NOERR

    def yearly(self, year, mailbox, dest):
        log.info('yearly(year: %s, mailbox: %s, dest: %s)', year, mailbox, dest)
        # check year
        try:
            year = int(year)
        except ValueError:
            raise ImapReorgError(ERREXPRARGS, 'invalid year value: <%s>' % year)

        # check or create dest mailbox
        ret, count = self._select(dest)
        if not ret:
            ret = self._create(dest)
            if not ret:
                raise ImapReorgError(ERREXPRARGS, 'failed to create mailbox <%s>' % dest)
            log.info('created mailbox <%s>', dest)
        else:
            log.info('mailbox <%s>: %s messages', dest, count)

        # check, if mailbox exists
        ret, count = self._select(mailbox)
        if not ret:
            raise ImapReorgError(ERREXPRARGS, 'mailbox <%s> doesn\'t exist' % mailbox)
        else:
            log.info('mailbox <%s>: %s messages', mailbox, count)

        # fetch matching mails
        ret, items = self._imap.box.uid('SEARCH', None, '(SINCE 01-Jan-%s BEFORE 01-Jan-%s)' % (year, year + 1))
        if ret == 'OK':
            log.debug('items: %s', items)
        else:
            log.debug('search: %s %s', ret, items)
            raise ImapReorgError(ERRPROT, 'searching in mailbox <%s> failed' % mailbox)

        # copy matching messages
        nr = 0
        uids = [uid.decode('utf-8') for uid in items[0].split()]
        uidset = []
        limit = self._limit if self._limit is not None else len(uids)
        while uids:
            uidset = uids[:limit]
            log.info('move %s of %s messages to %s', len(uidset), len(uids), dest)
            uids = uids[limit:]
            nr += len(uidset)
            copyres, delres = self._imap.move(','.join(uidset), dest)
            if copyres[0] != 'OK':
                raise ImapReorgError(ERRPROT, 'copying failed: %s' % str(copyres))
            if delres[0][0] != 'OK':
                raise ImapReorgError(ERRPROT, 'deleting failed: %s' % str(delres))

        # messages copied, expunge mailbox
        if nr:
            ret, data = self._imap.expunge()
            if ret != 'OK':
                raise ImapReorgError(ERRPROT, 'expunge <%s> failed' % mailbox)
            log.info('moved %s messages from <%s> to <%s>', nr, mailbox, dest)
        else:
            log.debug('no message dates matched %s in <%s>', year, mailbox)

        return NOERR


@trace()
def process():
    ret = 0
    started = time.time()
    log.info('started with pid %s', os.getpid())
    try:
        reorg = ImapReorg(gpar.user, gpar.password, gpar.server, gpar.port, gpar.ssl, gpar.limit)
        for expr in gpar.expr:
            ret |= reorg._run_expr(expr)
        reorg._logout()
    except ImapReorgError as e:
        log.exception(e)
        ret |= e.errcode

    log.info('finished with %s in %s', ret, fdeltat(time.time() - started))
    return ret


def main(argv = None):
    """Command line interface and console script entry point."""
    if argv is None:
        argv = sys.argv[1:]

    try:
        optlist, args = getopt.getopt(argv, 'hVvl:fsu:p:',
            ('help', 'version', 'verbose', 'logfile=',
             'force', 'ssl', 'user=', 'password=')
        )
    except getopt.error as msg:
        exit(1, msg, True)

    for opt, par in optlist:
        if opt in ('-h', '--help'):
            exit(usage = True)
        elif opt in ('-V', '--version'):
            exit(msg = 'version %s' % gpar.version)
        elif opt in ('-v', '--verbose'):
            if gpar.loglevel > logging.DEBUG:
                gpar.loglevel -= 10
        elif opt in ('-l', '--logfile'):
            gpar.logfile = par
        elif opt in ('-f', '--force'):
            gpar.force = True
        elif opt in ('-s', '--ssl'):
            gpar.ssl = False
        elif opt in ('-u', '--user'):
            gpar.user = par
        elif opt in ('-p', '--password'):
            gpar.password = par

    setup_logging(gpar.logfile, gpar.loglevel)

    if not args:
        exit(ERRARGS, 'no account specified', usage = True)

    try:
        gpar.server = args.pop(0)
        if not gpar.user:
            gpar.user, gpar.server = gpar.server.split('@', 1)
        if not gpar.password:
            gpar.user, gpar.password = gpar.user.split(':', 1)
        if ':' in gpar.server:
            gpar.server, gpar.port = gpar.server.split(':', 1)
            gpar.port = int(gpar.port)
    except ValueError as e:
        exit(ERRARGS, 'failed to parse account: %s' % e)

    if not args:
        exit(ERRARGS, 'no expression specified', usage = True)

    gpar.expr = args

    try:
        return process()
    except KeyboardInterrupt:
        return ERRARGS|ERRLOGIN


if __name__ == '__main__':
    sys.exit(main())

