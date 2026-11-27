# Pricing scan: the total price is at most what a cover pays

Let $C$ be a finite
set of vertices, let $r$ be rational residual weights with $r(v) \ge 0$ for every vertex
$v$, let $P$ be a rational number, and let $L$ be a list of edges (ordered pairs of
vertices) such that every pair $(u, v)$ in $L$ has $u \in C$ or $v \in C$. If the pricing
scan of $L$ from residual weights $r$ and total price $P$ ends with residual weights $r'$
and total price $P'$, then $P' - P \le \sum_{v \in C} (r(v) - r'(v))$.

Every edge has an endpoint in $C$, which pays that edge's price.
