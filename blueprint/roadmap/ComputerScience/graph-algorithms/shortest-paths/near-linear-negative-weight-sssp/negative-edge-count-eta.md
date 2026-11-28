# The negative-edge count eta of shortest paths and the B-shifted graph

Let $G=(V,E,w)$ be a directed graph with integer weights and $E^{neg}(G)=\{e\in E: w(e)<0\}$. Let $s\in V$ reach every vertex. For $v\in V$ define

$$
\eta_G(v;s)=\min\{|P\cap E^{neg}(G)| : P \text{ a shortest } s\text{-}v \text{ path in } G\}
$$

if $\mathrm{dist}_G(s,v)>-\infty$, and $\eta_G(v;s)=\infty$ otherwise; put $\eta(G;s)=\max_{v}\eta_G(v;s)$. When $s$ is the dummy source of $G_s$ (a new vertex with weight-$0$ edges to every vertex), write $\eta_G(v)$ and $\eta(G)$, and, for $v$ with $\mathrm{dist}_{G_s}(s,v)>-\infty$, let $P_G(v)$ be a shortest $s$-$v$ path in $G_s$ attaining $\eta_G(v)$; no such path is chosen when $\mathrm{dist}_{G_s}(s,v)=-\infty$, as a reachable negative cycle may leave $v$ with no shortest path.

For an integer $B\ge 1$, the *$B$-shifted graph* $G^B=(V,E,w^B)$ has $w^B(e)=w(e)+B$ if $w(e)<0$ and $w^B(e)=w(e)$ otherwise. If $w(e)\ge -2B$ for all $e$, then $w^B(e)\ge -B$ for all $e$.

## Depends on

- [Negative-weight single-source shortest paths with integer weights bounded below by -W](negative-weight-sssp-integer-weights.md)

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
