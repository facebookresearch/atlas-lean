# Result of doubly linked list deletion

Let $S$ be a store of $n$ cells, each empty or
holding a node (a payload with next and previous pointers, each an index or NIL), let $h$ be a
header (an index in $\{0, \dots, n-1\}$ or NIL), and let $x$ be an index whose cell holds a node
$X$ such that the cells at the predecessor $X.\mathrm{prev}$ and the successor $X.\mathrm{next}$
hold nodes whenever these pointers are not NIL. Let $T$ be $S$ if $X.\mathrm{prev}$ is NIL, and
otherwise $S$ with the next pointer of the node in cell $X.\mathrm{prev}$ set to
$X.\mathrm{next}$. Then List Delete on $S$, $h$ and $x$ returns the store equal to $T$ if
$X.\mathrm{next}$ is NIL, and otherwise to $T$ with the previous pointer of the node in cell
$X.\mathrm{next}$ of $T$ set to $X.\mathrm{prev}$, together with the header $h$ if
$X.\mathrm{prev}$ is not NIL and $X.\mathrm{next}$ if it is NIL. The successor's node is read
from $T$, so when $X.\mathrm{prev}$ and $X.\mathrm{next}$ are the same index (not NIL), both
pointer updates apply to its node.
