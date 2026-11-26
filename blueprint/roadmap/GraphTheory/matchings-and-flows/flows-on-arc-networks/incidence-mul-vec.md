# Incidence matrix times an arc vector is net inflow

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. Let $B$ be the signed incidence matrix of the network, $B_{ve} = [h(e) = v] - [t(e) = v]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise. For every $f : E \to \mathbb{R}$ and every $v \in V$,

$$(Bf)_v = \sum_{e \,:\, h(e) = v} f(e) - \sum_{e \,:\, t(e) = v} f(e),$$

the flow into $v$ minus the flow out of $v$. A loop at $v$ occurs in both sums.
