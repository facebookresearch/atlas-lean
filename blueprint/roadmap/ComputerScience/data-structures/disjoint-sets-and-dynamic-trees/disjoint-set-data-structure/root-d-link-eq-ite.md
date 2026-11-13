# Linking two roots by rank

Let $U$ be a union-find structure on $\{0, \dots, n-1\}$ and
let $x, y < n$ be roots of $U$, i.e. each is its own parent. Let $U'$ be obtained by linking $x$
and $y$ by rank: nothing changes if $x = y$; otherwise, if $\operatorname{rank}(y) <
\operatorname{rank}(x)$ then $y$ gets parent $x$, and if not then $x$ gets parent $y$ and, when
the two ranks are equal, the rank of $y$ increases by one. Then for every natural number $i$,
where the root of an index $i \ge n$ is $i$ itself: if the root of $i$ in $U$ is $x$ or $y$, the
root of $i$ in $U'$ is $x$ when $\operatorname{rank}(y) < \operatorname{rank}(x)$ and $y$
otherwise; if the root of $i$ in $U$ is neither $x$ nor $y$, its root in $U'$ is the same as in
$U$.
