# Action of a locked schedule

For $n$ transactions, numbered $0, \dots, n-1$, and a type $X$
of data items, an action of a locked schedule is one of three kinds: a read or write operation; a
lock request, in which a transaction $t$ acquires a lock on an item $x \in X$ in a lock mode $m$
(shared or exclusive); or a release, in which a transaction $t$ releases its lock on an item
$x \in X$.
