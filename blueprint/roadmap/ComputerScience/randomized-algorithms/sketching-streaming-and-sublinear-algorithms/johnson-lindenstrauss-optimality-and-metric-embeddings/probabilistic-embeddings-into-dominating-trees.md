# Probabilistic embedding of a metric into dominating tree metrics

Let $(X, d)$ be a finite metric space. A *probabilistic embedding into dominating tree metrics with expected stretch $\alpha$* is a probability distribution $\mathcal{D}$ over pairs $(T, \phi)$, where $T$ is a tree with positive edge lengths and $\phi : X \to V(T)$, with shortest-path metric $d_T$, such that for all $x, y \in X$

$$
d_T(\phi(x), \phi(y)) \ge d(x, y) \ \text{ for every } (T, \phi) \text{ in the support}, \qquad \mathbb{E}_{(T, \phi) \sim \mathcal{D}}\, d_T(\phi(x), \phi(y)) \le \alpha\, d(x, y).
$$

By linearity of expectation, an $\alpha$-stretch tree distribution turns a $\rho$-approximation algorithm on tree metrics into an expected $\alpha\rho$-approximation on $X$ for a minimization problem whose feasible solutions are shared by $(X, d)$ and the tree instances (they are specified by points of $X$ alone, as with medians chosen among the points of $X$) and whose objective is a nonnegative linear combination of distances between points of $X$: run the tree algorithm on the instance with metric $d_T(\phi(\cdot), \phi(\cdot))$ on $X$ and return its solution. A solution that uses Steiner vertices of $T$, such as a median at a vertex outside $\phi(X)$, is not feasible on $X$, so a tree algorithm that uses them needs a recovery step that turns its returned solution $S_T$ into a feasible solution $S_X$ on $X$. A sufficient condition for keeping the expected $\alpha\rho$ guarantee is the cross-metric inequality $\mathrm{cost}_{(X, d)}(S_X) \le \mathrm{cost}_{T}(S_T)$, since every feasible solution on $X$ is also feasible on the tree instance and, by domination, costs there at least its cost in $(X, d)$. The recovered solution need not have tree cost at most that of $S_T$: for three terminals at pairwise distance $1$ embedded as the leaves of a star with unit edges, the Steiner center has tree median cost $3$ and every leaf has tree median cost $4$, while a leaf costs only $2$ in $(X, d)$.

## Depends on

- [Tree metric](../../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md)
- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Sources

- Yair Bartal, "Probabilistic approximation of metric spaces and its algorithmic applications", FOCS (1996), Theorem 4.
- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A tight bound on approximating arbitrary metrics by tree metrics", STOC (2003); J. Comput. Syst. Sci. 69 (2004).
