# Inside components of small weak diameter the B-shifted negative-edge count halves

Let $G=(V,E,w)$ be a directed graph with integer weights, let $B$ be a positive integer with $w(e)\ge -2B$ for all $e\in E$, and let $\Delta\ge 2$ be an integer. Let $G^B_{\ge 0}$ be $G^B$ with every negative weight raised to $0$, let $E^{rem}\leftarrow\mathrm{LowDiamDecomposition}(G^B_{\ge 0},\lfloor\Delta B/2\rfloor)$, let $V_1,V_2,\dots$ be the strongly connected components of $G^B\setminus E^{rem}$, and let $H=\bigcup_i G[V_i]$, the subgraph of edges inside these components. If $G$ has no negative cycle, then $\eta(H^B)\le\Delta/2$, so $\eta(H^B)\le\lfloor\Delta/2\rfloor$.

## Proof sketch

Every component $V_i$ has weak diameter at most $\lfloor\Delta B/2\rfloor$ in $G^B_{\ge 0}$, and $w\le w^B\le w^B_{\ge 0}$ edgewise, so $\mathrm{dist}_G(u,v)\le\Delta B/2$ for all $u,v$ in a common $V_i$. Suppose a shortest path from the dummy source in $H^B_s$ to $v\in V_i$ attaining $\eta_{H^B}(v)$ uses $k>\Delta/2$ negative edges, and let $Q$ be its part inside $V_i$, from $u$ to $v$. Since $w^B(Q)\le 0$ and each of the $k$ edges negative in $H^B$ was raised by exactly $B$ (other edges by $B$ or $0$), one gets $w(Q)\le w^B(Q)-kB<-\Delta B/2$. Closing $Q$ with a $v$-$u$ walk of weight $\mathrm{dist}_G(v,u)\le\Delta B/2$ yields a negative cycle in $G$, a contradiction; the price-function invariance of cycle weights lets the same argument run after any reweighting.

## Depends on

- [The negative-edge count eta of shortest paths and the B-shifted graph](negative-edge-count-eta.md)
- [A weak directed low-diameter decomposition with overhead O(log^2 n) in near-linear time](bnw-weak-directed-ldd.md)

## Proof depends on

- [Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights](price-function-distance-shift.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456, Algorithm 1 (Phases 0 and 1), Lemmas 4.3 and 4.5.
