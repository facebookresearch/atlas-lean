# Connectivity of rNNI and rSPR moves on rooted networks

**Networks.** A binary rooted phylogenetic network on a leaf set $X$ is a directed acyclic graph with one root (indegree $0$, outdegree $1$), leaves labelled bijectively by $X$ (indegree $1$, outdegree $0$), bifurcations (indegree $1$, outdegree $2$) and reticulations (indegree $2$, outdegree $1$).

**Reticulate complexity.** For binary rooted networks $N_1, N_2$ on $X$ the following are equivalent: they have the same number $r$ of reticulations; the same number of vertices; the same number of arcs; the same number of arc removals needed to turn them into rooted trees. Indeed every such network has

$$n = 2\,(r + |X|) \text{ vertices}.$$

**rNNI move.** Say $N$ has an arc on $\{u, v\}$ if it contains $uv$ or $vu$. If $N$ has distinct vertices $s, u, v, t$ with arcs on $\{s,u\}$, $\{u,v\}$, $\{v,t\}$ and none on $\{u,t\}$, $\{s,v\}$, an rNNI move replaces the arcs on $\{s,u\}, \{u,v\}, \{v,t\}$ by arcs on $\{u,t\}, \{u,v\}, \{s,v\}$ such that (1) the in- and outdegrees of $s$ and $t$ are unchanged, (2) the in- and outdegrees of $u$ and $v$ stay at most $2$, and (3) the result is acyclic. The arc on $\{u,v\}$ may be reversed. rNNI moves preserve all vertex degrees, hence binarity and the number of reticulations; on trees they are ordinary rooted NNI moves.

**Theorem.**

1. Any two binary rooted phylogenetic networks on $X$ with the same number $r$ of reticulations are connected by a sequence of rNNI moves.
2. $N$ can be turned into $N'$ by one rNNI move if and only if it can be turned into $N'$ by one $\mathrm{rSPR}^1$ move (an rSPR move that prunes an arc and regrafts it at distance one).
3. Consequently, networks with the same number of reticulations are connected by rSPR moves, and their rSPR distance is at most their rNNI distance.

## Expansion

Counting degrees with $b$ bifurcations, total indegree $b + 2r + |X|$ equals total outdegree $1 + 2b + r$, so $b = r + |X| - 1$ and $n = 1 + b + r + |X| = 2(r + |X|)$. The connectivity proof passes through unrooted networks: unrooted NNI moves connect any two unrooted binary networks with the same number of vertices; each unrooted NNI on the underlying network of $N$ can be realised by rNNI moves on $N$; and two rooted networks with the same underlying unrooted network differ by orientations, which arc flips (reversing an arc from a bifurcation to a reticulation when no other path joins them) can fix, each flip costing two rNNI moves. Arc flips alone suffice for level-1 networks but not in general, so the general proof routes both networks to a common *flip-friendly* network with $r$ reticulations, which exists for every $X$ and $r \ge 1$. Separate "vertical" moves that add or remove one reticulation connect different complexity levels.

## Sources

- P. Gambette, L. van Iersel, M. Jones, M. Lafond, F. Pardi, C. Scornavacca, "Rearrangement moves on rooted phylogenetic networks", PLoS Computational Biology 13 (2017) e1005611, Results (Proposition 1; Definition 1, rNNI; Lemmas 1–5; Theorems 2–3, rNNI connectivity; Theorem 4 and Corollary 1, rNNI versus rSPR), <https://doi.org/10.1371/journal.pcbi.1005611> (PMC5557604).
