# Probabilistic embedding of a metric into dominating tree metrics

Let $(X, d)$ be a finite metric space. A *probabilistic embedding into dominating tree metrics with expected stretch $\alpha$* is a probability distribution $\mathcal{D}$ over pairs $(T, \phi)$, where $T$ is a tree with positive edge lengths and $\phi : X \to V(T)$, with shortest-path metric $d_T$, such that for all $x, y \in X$

$$
d_T(\phi(x), \phi(y)) \ge d(x, y) \ \text{ for every } (T, \phi) \text{ in the support}, \qquad \mathbb{E}_{(T, \phi) \sim \mathcal{D}}\, d_T(\phi(x), \phi(y)) \le \alpha\, d(x, y).
$$

By linearity of expectation, an $\alpha$-stretch tree distribution turns a $\rho$-approximation algorithm on trees for a problem with a nonnegative linear objective in the distances into an expected $\alpha\rho$-approximation on $X$.

## Depends on

- [Tree metric](../../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md)
- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Sources

- Yair Bartal, "Probabilistic approximation of metric spaces and its algorithmic applications", FOCS (1996).
- Jittat Fakcharoenphol, Satish Rao, Kunal Talwar, "A tight bound on approximating arbitrary metrics by tree metrics", STOC (2003); J. Comput. Syst. Sci. 69 (2004).
