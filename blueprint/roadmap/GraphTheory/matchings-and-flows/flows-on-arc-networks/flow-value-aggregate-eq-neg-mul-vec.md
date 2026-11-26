# Flow value of an aggregated arc vector

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. Let $B$ be the signed incidence matrix of the network, $B_{ve} = [h(e) = v] - [t(e) = v]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise. For $f : E \to \mathbb{R}$ write $\bar f(p, q) = \sum_{e \,:\, t(e) = p,\ h(e) = q} f(e)$ for the total of $f$ over the arcs from $p$ to $q$. For every $f : E \to \mathbb{R}$ and $s \in V$, the value of $\bar f$ at $s$ is minus the net inflow of $f$ at $s$:

$$\sum_{v \in V} \bar f(s, v) - \sum_{p \in V} \bar f(p, s) = -(Bf)_s.$$

No feasibility or sign condition on $f$ is assumed.
