# Ranks grow along nonroot parent steps

Let $u$ be a union-find state with stored parent map $p$ on $\mathbb{N}$ and stored ranks $r$,
and let $x, k \in \mathbb{N}$. If $p^j(x)$ is not a root (that is, $p(p^j(x)) \ne p^j(x)$)
for every $j < k$, then $r(x) + k \le r(p^k(x))$.
