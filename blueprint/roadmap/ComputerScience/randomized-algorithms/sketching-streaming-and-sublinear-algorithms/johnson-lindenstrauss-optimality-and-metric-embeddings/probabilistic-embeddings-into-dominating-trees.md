# Probabilistic embedding of a metric into dominating tree metrics

Let $(X, d)$ be a finite metric space. A *probabilistic embedding into dominating tree metrics with expected stretch $\alpha$* is a probability distribution $\mathcal{D}$ over pairs $(T, \phi)$, where $T$ is a tree with positive edge lengths and $\phi : X \to V(T)$, with shortest-path metric $d_T$, such that for all $x, y \in X$

$$
d_T(\phi(x), \phi(y)) \ge d(x, y) \ \text{ for every } (T, \phi) \text{ in the support}, \qquad \mathbb{E}_{(T, \phi) \sim \mathcal{D}}\, d_T(\phi(x), \phi(y)) \le \alpha\, d(x, y).
$$

By linearity of expectation, an $\alpha$-stretch tree distribution turns a $\rho$-approximation algorithm on tree metrics into an expected $\alpha\rho$-approximation on $X$ for a minimization problem whose feasible solutions are shared by $(X, d)$ and the tree instances (they are specified by points of $X$ alone, as with medians chosen among the points of $X$) and whose objective is a nonnegative linear combination of distances between points of $X$: run the tree algorithm on the instance with metric $d_T(\phi(\cdot), \phi(\cdot))$ on $X$ and return its solution. A solution that uses Steiner vertices of $T$, such as a median at a vertex outside $\phi(X)$, is not feasible on $X$, so a tree algorithm that uses them can be applied only together with a recovery step that turns its solution into a feasible solution on $X$ without increasing its tree cost.

## Depends on

- [Tree metric](../../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md)
- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Sources

- Yair Bartal, "Probabilistic approximation of metric spaces and its algorithmic applications", FOCS (1996), Theorem 4.
- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A tight bound on approximating arbitrary metrics by tree metrics", STOC (2003); J. Comput. Syst. Sci. 69 (2004).
