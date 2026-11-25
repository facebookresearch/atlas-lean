# Endpoint-pair aggregation of an arc function

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. For $f : E \to \mathbb{R}$ and $p, q \in V$, the endpoint-pair aggregate of $f$ is

$$\bar f(p, q) = \sum_{e \,:\, t(e) = p,\ h(e) = q} f(e),$$

the total of $f$ over the arcs from $p$ to $q$ (zero when there are none). It turns arc capacities or arc flows into functions on $V \times V$.
