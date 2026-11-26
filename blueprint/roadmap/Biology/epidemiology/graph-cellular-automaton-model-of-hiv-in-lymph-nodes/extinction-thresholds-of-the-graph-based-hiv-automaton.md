# Extinction thresholds of the graph-based HIV cellular automaton

**Model (Mukwembi).** A lymph node is a finite simple graph $G = (V, E)$ whose vertices are cell sites. A state is a map $f : V \to \{0, 1, 2\}$ (healthy, infected, dead); admissible initial states $f_0 \in \Omega_0(G)$ have no dead cells. Fix a **replacement parameter** $R \in \mathbb Z^+$. All vertices update synchronously:

- a healthy cell becomes infected if it has at least one infected neighbor, and otherwise stays healthy;
- an infected cell dies;
- a dead cell is replaced by an infected cell if it has at least $R$ infected neighbors, and by a healthy cell otherwise.

The infection **becomes extinct** on $(G, f_0)$ under $R$ if the all-healthy state $\mathbf 0_G$ (a fixed point) is reached; otherwise it is **latent**. Let $\mathcal E(G)$ be the set of $R$ for which every admissible $f_0$ leads to extinction, and define the first extinction value and the eventual extinction threshold

$$\mathrm{hiv}(G) = \min \mathcal E(G), \qquad \mathrm{HIV}(G) = \min\{R_0 : R \in \mathcal E(G) \text{ for all } R \ge R_0\}.$$

Extinction need not be monotone in $R$, so the two can differ. Let $\Delta(G)$ and $\delta(G)$ be the maximum and minimum degrees.

**Theorem.**

1. If $G$ has at least one edge, then $2 \le \mathrm{hiv}(G) \le \mathrm{HIV}(G) \le \Delta(G) + 1$.
2. If $G$ is bipartite with $\delta(G) \ge 1$, then $\mathrm{hiv}(G) \ge \delta(G) + 1$.
3. For connected $G$ with at least one edge, $\mathrm{HIV}(G) = \Delta(G) + 1$ if and only if $G$ is bipartite and regular, and then $\mathrm{hiv}(G) = \mathrm{HIV}(G) = \Delta(G) + 1$.
4. For every $k \ge 2$ there is a connected graph with $\mathrm{HIV}(G) - \mathrm{hiv}(G) = k$.
5. Exact values: $\mathrm{HIV}(C_n) = \mathrm{hiv}(C_n) = 3$ for even $n$ and $2$ for odd $n$ ($n \ge 3$); $\mathrm{HIV}(K_n) = \mathrm{hiv}(K_n) = \lceil (n+1)/2 \rceil$; and for $m \le n$, $\mathrm{HIV}(K_{m,n}) = \mathrm{hiv}(K_{m,n}) = \max\{m+1, \lfloor n/2 \rfloor + 1\}$.

**Theorem (two-cycles).** The $R$-state transition digraph has a cycle of length $2$ if and only if $V = U_0 \cup U_1$ can be partitioned so that every vertex of $U_0$ has at least $R$ neighbors in $U_1$ and every vertex of $U_1$ has at least $R$ neighbors in $U_0$. For every $n \ge 1$ there are $G$, $R$ and $f_0$ whose trajectory ends in a cycle of length $n$.

These results sharpen Mukwembi's theorem that extinction always occurs for $R = n - 1$ on an $n$-vertex graph: latency (persistent reinfection) requires dense, nearly bipartite neighborhoods, and the threshold is governed by the maximum degree.

## Expansion

Latency for $R$ forces some vertex to be dead at time $t$ and reinfected at time $t+1$, which needs $R$ infected neighbors; since a vertex has at most $\Delta(G)$ neighbors, every $R \ge \Delta(G) + 1$ gives extinction. On a bipartite regular graph, infecting one side makes the two sides alternate between infected and dead/reinfected forever when $R = \Delta$, which is exactly the two-cycle criterion with $U_0, U_1$ the bipartition; conversely, a latent configuration at $R = \Delta$ forces such a partition with all degrees equal to $\Delta$. The lower bound for bipartite graphs uses the same alternating construction with the minimum degree. The family values come from analyzing which alternating or rotating patterns survive on cycles, cliques and complete bipartite graphs.

## Sources

- Manuel A. Espinosa-García, Ana Paulina Figueroa, Julián A. Fresán-Figueroa, Gerardo L. Maldonado, "Extinction thresholds in a graph-based model of HIV infection dynamics", arXiv (2026). Section 2 (definitions), Theorem 2.1 (Mukwembi), Proposition 2.5, Theorems 2.6, 2.8–2.11, 3.3, 3.4, 4.1–4.3. <https://doi.org/10.48550/arXiv.2608.00340>
