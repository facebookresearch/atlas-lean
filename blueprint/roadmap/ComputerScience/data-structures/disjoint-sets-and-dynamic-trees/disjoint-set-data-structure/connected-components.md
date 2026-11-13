# Connected components via union-find

Given a natural number $n$ and a list $E$ of pairs
of vertices in $\{0, \dots, n-1\}$, CONNECTED-COMPONENTS first builds the union-find structure
with $n$ singleton nodes $0, \dots, n-1$ by $n$ MAKE-SET calls. It then processes the pairs
$(u, v)$ of $E$ in list order: it asks whether $u$ and $v$ are equivalent using two FIND-SET
calls, keeping the path compression done by the query, and if they are not equivalent it
performs UNION on $u$ and $v$ (union by rank with path compression). It returns the final
union-find structure, which has $n$ nodes, together with the numbers of MAKE-SET, FIND-SET and
UNION calls made.
