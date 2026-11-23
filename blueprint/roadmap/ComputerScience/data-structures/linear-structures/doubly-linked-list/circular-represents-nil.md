# Empty circular list with a sentinel

Let $S$ be a store of $n$ slots indexed by
$\{0, \dots, n-1\}$, each either empty or holding a node with a payload and optional next and
previous indices, and let $s$ be an index. Then $S$ represents the empty circular list with
sentinel $s$ if and only if slot $s$ holds a node whose next index and previous index are both
$s$.
