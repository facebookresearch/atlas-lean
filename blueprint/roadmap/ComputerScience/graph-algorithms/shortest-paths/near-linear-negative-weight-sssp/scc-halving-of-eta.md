# Inside components of small weak diameter the B-shifted negative-edge count halves

Let $G=(V,E,w)$ have integer weights with $w(e)\ge -2B$ and no negative cycle, let $\Delta\ge 2$, and let $V_1,V_2,\dots$ be disjoint vertex sets with $\mathrm{dist}_G(u,v)\le \Delta B/2$ for all $u,v$ in a common $V_i$. Let $H=\bigcup_i G[V_i]$ be the union of the induced subgraphs. Then $\eta(H^B)\le\Delta/2$.

## Proof sketch

Suppose a shortest path from the dummy source in $H^B_s$ to $v\in V_i$ attaining $\eta_{H^B}(v)$ uses $k>\Delta/2$ negative edges, and let $Q$ be its part inside $V_i$, from $u$ to $v$. Since $w^B(Q)\le 0$ and each of the $k$ edges negative in $H^B$ was raised by exactly $B$ (other edges by $B$ or $0$), one gets $w(Q)\le w^B(Q)-kB<-\Delta B/2$. Closing $Q$ with a $v$-$u$ walk of weight $\mathrm{dist}_G(v,u)\le\Delta B/2$ yields a negative cycle in $G$, a contradiction; the price-function invariance of cycle weights lets the same argument run after any reweighting.

## Depends on

- [The negative-edge count eta of shortest paths and the B-shifted graph](negative-edge-count-eta.md)

## Proof depends on

- [Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights](price-function-distance-shift.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
