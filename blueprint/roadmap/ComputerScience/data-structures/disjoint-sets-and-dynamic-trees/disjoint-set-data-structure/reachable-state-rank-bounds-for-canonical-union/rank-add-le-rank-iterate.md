# Ranks grow along nonroot parent steps

Let $u$ be a union-find state with stored parent map $p$ on $\mathbb{N}$ and stored ranks $r$. Every union-find state, reachable or not, satisfies $r(z) < r(p(z))$ for every nonroot $z$ (a node with $p(z) \ne z$); this invariant is part of the structure. For $x, k \in \mathbb{N}$, if $p^j(x)$ is not a root (that is, $p(p^j(x)) \ne p^j(x)$) for every $j < k$, then $r(x) + k \le r(p^k(x))$.
