# Spanning tree polytope of a connected graph

Let $G=(V,E)$ be a connected edge-indexed multigraph (parallel edges are distinct elements of $E$, loops are excluded) with $n=|V| \ge 2$. A spanning tree of $G$ is a set $T \subseteq E$ of $n-1$ edges containing no cycle, so that $(V,T)$ is connected; it contains at most one edge from each class of parallel edges. For $S \subseteq V$ let $E(S)$ denote the set of edges with both endpoints in $S$, and for $z \in \mathbb{R}^E$ and $F \subseteq E$ write $z(F)=\sum_{e \in F} z_e$. The spanning tree polytope of $G$ is

$$
P_{\mathrm{ST}}(G)=\{z \in \mathbb{R}_{\ge 0}^{E} : z(E)=n-1,\ z(E(S)) \le |S|-1 \ \text{for all}\ \emptyset \ne S \subsetneq V\}.
$$

Edmonds showed that $P_{\mathrm{ST}}(G)$ is the convex hull of the indicator vectors $\mathbf{1}_T$ of the spanning trees $T$ of $G$; it is the base polytope of the graphic matroid of $G$, whose bases are the spanning trees. Consequently, for every cost vector $c \in \mathbb{R}^E$, the minimum cost of a spanning tree equals $\min\{c^{\top}z : z \in P_{\mathrm{ST}}(G)\}$.

## Proof sketch

Every $\mathbf{1}_T$ lies in $P_{\mathrm{ST}}(G)$: $|T| = n-1$, and $T \cap E(S)$ is a forest on the vertex set $S$, so it has at most $|S|-1$ edges. For the converse, let $r(F) = n - \kappa(F)$ for $F \subseteq E$, where $\kappa(F)$ is the number of connected components of $(V,F)$. Every $z \in P_{\mathrm{ST}}(G)$ satisfies $z(F) \le r(F)$: if $S_1, \dots, S_\kappa$ are the vertex sets of the components of $(V,F)$, then $F \subseteq \bigcup_j E(S_j)$, so $z \ge 0$ and the constraints give $z(F) \le \sum_j z(E(S_j)) \le \sum_j (|S_j|-1) = r(F)$, where $z(E(V)) = z(E) = n-1$ is used if some $S_j = V$, and $E(S_j) = \emptyset$ if $|S_j| = 1$. Now fix $c \in \mathbb{R}^E$, order the edges as $e_1, \dots, e_m$ with $c(e_1) \le \dots \le c(e_m)$, and let $E_i = \{e_1, \dots, e_i\}$, $E_0 = \emptyset$. The greedy algorithm that scans $e_1, \dots, e_m$ and keeps $e_i$ exactly when it joins two components of the edges kept so far returns a spanning tree $T$ with $|T \cap E_i| = r(E_i)$ for every $i$, since by induction the kept edges among $E_i$ have the same components as $E_i$; hence $r(E_i) - r(E_{i-1})$ is $1$ if $e_i \in T$ and $0$ otherwise. Summation by parts, with $c(e_i) - c(e_{i+1}) \le 0$, $z(E_i) \le r(E_i)$ and $z(E_m) = n-1 = r(E_m)$, gives for every $z \in P_{\mathrm{ST}}(G)$

$$
c^{\top}z = \sum_{i=1}^{m-1}\big(c(e_i) - c(e_{i+1})\big)\,z(E_i) + c(e_m)\,z(E_m) \ge \sum_{i=1}^{m-1}\big(c(e_i) - c(e_{i+1})\big)\,r(E_i) + c(e_m)\,r(E_m) = c(T).
$$

So the linear program and the spanning trees have the same minimum for every $c$. This alone does not exclude fractional vertices; separation does. The set $Q = \mathrm{conv}\{\mathbf{1}_T\}$ is nonempty (as $G$ is connected), compact, convex and contained in $P_{\mathrm{ST}}(G)$. If some $z^* \in P_{\mathrm{ST}}(G)$ were outside $Q$, strict separation of $z^*$ from $Q$ would give $c$ with $c^{\top}z^* < \min_{y \in Q} c^{\top}y = \min_T c(T)$, contradicting the inequality above. Hence $P_{\mathrm{ST}}(G) = Q$.

## Depends on

- [Edge-indexed multigraph](../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/edge-indexed-multigraph.md)

## Proof depends on

- [Strict separation of a point from a closed convex set](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/strict-separation-of-a-point-from-a-closed-convex-set.md)

## Sources

- Jack Edmonds, "Matroids and the Greedy Algorithm", Mathematical Programming (1971).
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Section 2.2, equation (2).
