# The Khandekar-Rao-Vazirani cut-matching game

Fix an even $n$ and a vertex set $V$ with $|V| = n$. The *cut-matching game* is played for $T$ rounds between a *cut player* and a *matching player*, starting from the empty graph $H_0 = (V, \emptyset)$. In round $t \in \{1, \dots, T\}$:

1. the cut player, seeing $H_{t-1}$, chooses a bisection $(S_t, V \setminus S_t)$ with $|S_t| = n/2$;
2. the matching player chooses an arbitrary perfect matching $M_t$ between $S_t$ and $V \setminus S_t$;
3. $H_t = H_{t-1} + M_t$ (edges are added with multiplicity).

The *edge expansion* of a multigraph $H$ on $V$ is $h(H) = \min_{\emptyset \ne S \subseteq V, \, |S| \le n/2} |E_H(S, V \setminus S)| / |S|$. The cut player wins after $T$ rounds with expansion target $\gamma > 0$ if $h(H_T) \ge \gamma$, whatever the matching player does. In the algorithmic use, each matching is routed by a single-commodity flow in the input graph, so that $H_T$ embeds into the input graph with bounded congestion.

## Sources

- Rohit Khandekar, Satish Rao, Umesh Vazirani, "Graph Partitioning using Single Commodity Flows", STOC (2006); J. ACM 56(4) (2009).
- Lorenzo Orecchia, Leonard J. Schulman, Umesh V. Vazirani, Nisheeth K. Vishnoi, "On Partitioning Graphs via Single Commodity Flows", STOC (2008).
