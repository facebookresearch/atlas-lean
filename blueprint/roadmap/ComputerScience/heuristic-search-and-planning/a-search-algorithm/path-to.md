# Path recovered from an A-star result

Given an A* result $r$ on $n$ vertices and a vertex
$v$, follow the predecessor pointers of the underlying Dijkstra search backward from $v$, at most
$n$ times, until the source is reached, and return the visited vertices in order from the source
to $v$. There is no result if a vertex without a predecessor is met before the source, or if the
source is not reached within $n$ steps.
