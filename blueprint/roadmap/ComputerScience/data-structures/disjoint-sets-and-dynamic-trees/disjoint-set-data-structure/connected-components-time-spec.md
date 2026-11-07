# Operation counts of connected components

Let $n$ be a natural number, let $E$ be a list
of pairs of vertices in $\{0, \dots, n-1\}$ and let $m$ be the length of $E$. Let $G$ be the
simple graph on $\{0, \dots, n-1\}$ whose edges are the unordered pairs $\{u, v\}$ with $(u, v)$
in $E$ and $u \ne v$, and let $k$ be the number of connected components of $G$. Running
CONNECTED-COMPONENTS on $n$ and $E$ makes exactly $n$ MAKE-SET calls, $2m$ FIND-SET calls and
$n - k$ UNION calls. Moreover, $k$ plus the number of UNION calls equals $n$, and if $n > 0$
then the number of UNION calls is at most $n - 1$.

These are the call counts recorded by the cost annotation, not bounds on parent-pointer visits.
