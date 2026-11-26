# Stable sample compression schemes

A sample compression scheme of size $k$ for a class $H \subseteq \{0,1\}^X$ consists of a compression map $\kappa$ sending each realizable labelled sample $S$ to a subsample $\kappa(S) \subseteq S$ with $|\kappa(S)| \le k$, and a reconstruction map $\rho$ such that $\rho(\kappa(S))$ is correct on every example of $S$. The scheme is **stable** if for every realizable $S$ and every $S'$ with $\kappa(S) \subseteq S' \subseteq S$ one has $\kappa(S') = \kappa(S)$: removing examples that were not kept does not change the compressed set (and hence the output).

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
