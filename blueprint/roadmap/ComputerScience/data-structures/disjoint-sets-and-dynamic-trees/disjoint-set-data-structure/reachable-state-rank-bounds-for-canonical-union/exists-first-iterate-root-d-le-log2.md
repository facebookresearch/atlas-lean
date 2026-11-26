# First root on a parent chain within log₂ of the size

Let $u$ be a union-find state of size $n$ that is reachable from the empty state by the
canonical operations, and let $x < n$ be an allocated node. Then there is $d$ such that
$p^d(x)$ is the root of $x$, $p^k(x)$ differs from that root for every $k < d$, and
$d \le \lfloor \log_2 n \rfloor$, where $p$ is the stored parent map of $u$.
