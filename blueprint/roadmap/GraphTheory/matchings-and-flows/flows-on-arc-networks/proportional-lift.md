# Proportional lift of an endpoint-pair flow to the arcs

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. For $f : E \to \mathbb{R}$ write $\bar f(p, q) = \sum_{e \,:\, t(e) = p,\ h(e) = q} f(e)$ for the total of $f$ over the arcs from $p$ to $q$. Given arc capacities $u : E \to \mathbb{R}$ and $F : V \times V \to \mathbb{R}$, the proportional lift of $F$ is the arc function

$$\hat F(e) = \begin{cases} 0 & \text{if } \bar u(t(e), h(e)) = 0, \\ F(t(e), h(e))\, u(e) / \bar u(t(e), h(e)) & \text{otherwise.} \end{cases}$$

On each endpoint pair with nonzero total capacity $\bar u(p, q) \ne 0$, this splits the value $F(p, q)$ among the parallel arcs of that pair in proportion to their capacities, so that $\bar{\hat F}(p, q) = F(p, q)$. On a pair with zero total capacity it returns $0$ regardless of $F$: for one arc of capacity $0$ whose endpoint pair has $F = 1$, the lift is $0$ on the arc. Recovering $F$ on every pair needs $F$ to vanish on the zero-capacity pairs.
