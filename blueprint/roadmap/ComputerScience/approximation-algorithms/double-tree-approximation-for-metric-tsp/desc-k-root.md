# Every non-root vertex lies below the root

Let $p$ assign to each vertex of
$\{0, \dots, n-1\}$ either a parent or nothing, forming a parent tree with root $r$, and let a
step up move a vertex to its parent, leaving a vertex without parent in place. Then every vertex
$u \ne r$ lies strictly below $r$, at most $n$ levels down: for some $j < n$, the vertex reached
from $u$ after $j$ steps up has parent $r$.
