# First root on a parent chain within the rank gap

Let $u$ be any union-find state of size $n$ (not necessarily reachable), with stored parent
map $p$ and stored ranks $r$, and let $x < n$. Then there is $d$ such that $p^d(x)$ is the
root of $x$, $p^k(x)$ differs from that root for every $k < d$, and
$r(x) + d \le r(\mathrm{root}(x))$.
