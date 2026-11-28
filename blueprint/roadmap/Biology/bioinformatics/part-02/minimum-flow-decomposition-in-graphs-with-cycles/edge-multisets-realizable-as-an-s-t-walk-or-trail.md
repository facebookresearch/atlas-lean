# Edge multisets realizable as a single s-t walk or trail

**Setting.** A **flow network** $G=(V,E,f)$ is a directed graph (cycles allowed) with unique source $s$ and sink $t$ and positive integer edge flows $f_{uv}$ satisfying conservation at every $v \ne s,t$. A **$k$-flow decomposition** is a family of $k$ walks $W_1,\dots,W_k$ with weights $w_i \in \mathbb Z_{>0}$ such that $\sum_{i=1}^k w_i W_i(u,v) = f_{uv}$ for every edge, where $W_i(u,v)$ is the number of traversals of $(u,v)$ by $W_i$. **Minimum flow decomposition** (MFD) asks for the least $k$, with the walks restricted to $s$-$t$ paths or cycles (FDPC), $s$-$t$ trails (no repeated edge, FDT), or arbitrary $s$-$t$ walks (FDW). MFD is NP-hard already on acyclic graphs. For a multiset $W$ of edges write $\Delta_W(v) = \sum_{(u,v)\in E} W(u,v) - \sum_{(v,u)\in E} W(v,u)$ (in-multiplicity minus out-multiplicity), and call condition (B) the balance condition $\Delta_W(v) = 0$ for $v\notin\{s,t\}$, $\Delta_W(t)=1$, $\Delta_W(s)=-1$.

**Lemma (walks, Lemma 2).** The edges of a multiset $W$ can be ordered into an $s$-$t$ walk traversing each $(u,v)$ exactly $W(u,v)$ times if and only if (B) holds and every node incident to an edge of $W$ is reachable from $s$ using only edges of $W$.

**Lemma (trails, Lemma 1).** For a set $W$ of edges (multiplicities in $\{0,1\}$), the edges can be ordered into an $s$-$t$ trail if and only if (B) holds and every strongly connected component $C \ne \{t\}$ of the subgraph induced by $W$ has an edge of $W$ leaving $C$.

**ILP encoding (Lemma 3).** For walk $i$ take integer traversal counts $x_{uvi}\ge0$ ($x_{uvi}\in\{0,1\}$ for trails), at most one unit leaving $s$, and conservation at internal nodes. Add integer labels $d_{vi}\ge0$ with $d_{si}=1$ and $d_{vi}=0$ whenever $v$ has no selected in-edge, and binaries $y_{uvi}$ selecting, for each selected node $v\ne s$, exactly one selected in-edge $(u,v)$ with $d_{vi} \ge d_{ui}+1$. These constraints are feasible if and only if the two conditions of the walk lemma hold. Combined with the product linearization of $w_i x_{uvi}$ and the flow equations, this gives an exact ILP for $k$-FDW and $k$-FDT; minimizing over $k$ solves MFD on cyclic graphs.

## Expansion

Necessity of (B) is the usual degree count along a walk. For sufficiency in the walk case, add a return edge $(t,s)$: (B) makes the multigraph Eulerian-balanced and reachability from $s$ makes its support connected, so an Euler circuit exists; deleting the return edge gives the $s$-$t$ walk. The trail case is the same with multiplicity one, and the outgoing-edge condition on strongly connected components is the trail analogue of reachability (each component except $\{t\}$ must be exited). In the ILP, the labels $d$ strictly increase along the selected in-edges, so the selected edges form a spanning arborescence rooted at $s$ over all selected nodes, which is exactly reachability; conversely a BFS tree from $s$ supplies feasible $d$ and $y$.

## Sources

- F. H. C. Dias, L. Williams, B. Mumey and A. I. Tomescu, "Minimum flow decomposition in graphs with cycles using integer linear programming", arXiv:2209.00042 (2022), Section 2 (Definitions 1–4) and Section 3 (Lemmas 1–3), <https://doi.org/10.48550/arXiv.2209.00042>.
