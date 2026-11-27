# Co-linear chaining on cyclic pangenome graphs

Let $G = (V, E, \sigma)$ be a pangenome graph, each vertex $v$ labelled by a string $\sigma(v)$ over $\{A,C,G,T\}$, possibly with cycles, and let $Q$ be a query read. An **anchor** $M[j] = (v, [x..y], [c..d])$ records that $\sigma(v)[x..y]$ matches $Q[c..d]$. Let $D(v_1,v_2)$ be the shortest-path character distance (edge $(v,u)$ has length $|\sigma(v)|$) and $D^\circ(v)$ the length of the shortest proper cycle through $v$. Anchor $M[i]$ **precedes** $M[j]$ if $M[i].d < M[j].c$ and either $M[i].v \ne M[j].v$ and $M[i].v$ reaches $M[j].v$, or $M[i].v = M[j].v$ and ($M[i].y < M[j].x$ or $v$ lies on a proper cycle). A **chain** is a sequence of anchors each preceding the next, with score

$$\sum_{j=1}^{q} \mathrm{weight}(s_j) - \sum_{j=1}^{q-1}\big(\mathrm{gap}_Q(s_j,s_{j+1}) + \mathrm{gap}_G(s_j,s_{j+1})\big),$$

where $\mathrm{gap}_Q$ is the query gap and $\mathrm{gap}_G(s_j,s_{j+1}) = s_{j+1}.x - s_j.y - 1$ plus $D(s_j.v, s_{j+1}.v)$ between different vertices, plus $0$ for ordered anchors on one vertex, and plus $D^\circ(s_j.v)$ when the chain must go around a cycle to revisit a vertex.

**Lemma (exact).** With the exact distances, the optimal chain score is computable in $\Theta(|V||E| + |V|^2\log|V| + N^2)$ time (all-pairs Dijkstra plus quadratic dynamic programming over sorted anchors).

**Path-cover formulation.** Fix a path cover $\mathcal{P}$ (paths covering every vertex; computing a minimum one is NP-hard on cyclic graphs, but a lower bound follows from a minimum-flow computation) and replace $D$ by the distance $D_{\mathcal{P}}$ measured through the last vertex on each path that reaches the target (**last2reach**).

**Lemma (preprocessing).** Iterative relaxation of last2reach ranks and distances converges within $|V|$ iterations; preprocessing takes $O((\Gamma_l + \Gamma_d + \log|V|)\,|\mathcal{P}|\,|E|)$ time, where $\Gamma_l, \Gamma_d$ are the iteration counts used.

**Lemma (chaining).** Maintaining one range-maximum search tree per path and sweeping vertices by rank in rounds, the chaining scores converge to the optimum in at most $N$ rounds, and $\Omega(N)$ rounds can be necessary in the worst case. With $\Gamma_c$ rounds the total time is

$$O\big(\Gamma_c\,|\mathcal{P}|\,N\log N + |\mathcal{P}|\,N\log(|\mathcal{P}|N)\big)$$

and space $O(N|\mathcal{P}| + |V||\mathcal{P}|)$; on a DAG one round suffices and the method reduces to width-parameterized DAG chaining.

## Proof depends on

- [FASTER-APSP computes shortest-path weights](../../../../ComputerScience/graph-algorithms/shortest-paths/all-pairs-shortest-paths-by-min-plus-products/faster-apsp-distance-spec.md)

## Expansion

On a DAG, processing vertices in topological order guarantees that every predecessor anchor is final before it is queried. Cycles destroy this order, so the algorithm instead repeats rounds: after round $i$, every chain with at most $i$ anchors is already scored correctly (induction on chain size), and a chain has at most $N$ anchors, which gives convergence. Range-maximum queries over query coordinates $M[j].d$ in each path's search tree find the best predecessor reachable through that path in logarithmic time. Pangenome graphs have small path covers and converge in few rounds in practice, which makes long-read alignment to cyclic human pangenome graphs feasible.

## Sources

- J. Rajput, G. Chandra and C. Jain, "Co-linear chaining on pangenome graphs", Algorithms for Molecular Biology 19 (2024), Definitions 1–2, Problems 1–2, Lemmas 1–6 and Algorithms 1–3, <https://doi.org/10.1186/s13015-024-00250-w>, PMCID: PMC11288099.
