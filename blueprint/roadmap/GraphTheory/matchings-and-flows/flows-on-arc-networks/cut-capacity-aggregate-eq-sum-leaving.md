# Cut capacity of aggregated arc capacities

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. For $f : E \to \mathbb{R}$ write $\bar f(p, q) = \sum_{e \,:\, t(e) = p,\ h(e) = q} f(e)$ for the total of $f$ over the arcs from $p$ to $q$. For every $u : E \to \mathbb{R}$ and every subset $S \subseteq V$,

$$\sum_{p \in S} \sum_{q \in V \setminus S} \bar u(p, q) = \sum_{e \,:\, t(e) \in S,\ h(e) \notin S} u(e),$$

the total capacity of the arcs leaving $S$. No sign condition on $u$ is assumed; loops never leave $S$, and an arc entering $S$ does not count.
