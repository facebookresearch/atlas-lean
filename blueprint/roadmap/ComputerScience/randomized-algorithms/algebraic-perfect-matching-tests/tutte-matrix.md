# The Tutte matrix of a graph

Let $G$ be a finite simple graph on a linearly ordered vertex set $\{1, \dots, n\}$. Its **Tutte matrix** $T_G$ has one indeterminate $x_{\{i,j\}}$ per unordered pair, with $(T_G)_{ij} = x_{\{i,j\}}$ if $ij \in E(G)$ and $i < j$, $(T_G)_{ij} = -x_{\{i,j\}}$ if $ij \in E(G)$ and $i > j$, and $0$ otherwise. It is skew-symmetric, and $\det T_G$ has total degree at most $n$.

## Depends on

- [Perfect matching](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/perfect-matching.md)

## Sources

- W. T. Tutte, "The Factorization of Linear Graphs", Journal of the London Mathematical Society 22, 1947.
- L. Lovász, "On Determinants, Matchings, and Random Algorithms", Fundamentals of Computation Theory (FCT 1979), Akademie-Verlag, 1979.
