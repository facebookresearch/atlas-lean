# Operation of a schedule

For $n$ transactions, numbered $0, \dots, n - 1$, and data items
of type $X$, an operation consists of a transaction $t \in \{0, \dots, n - 1\}$, an occurrence
identifier $k \in \mathbb{N}$, an access, which is a read or a write, and a data item $x \in X$:
transaction $t$ reads or writes $x$, and $k$ makes repeated accesses of $t$ to an item distinct
operations.
