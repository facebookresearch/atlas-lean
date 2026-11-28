# Spectral sparsification

A graph $H$ is a spectral approximation of $G$ when $L_G \preceq L_H \preceq \kappa L_G$ in the Loewner order, so that every Laplacian quadratic form, and hence every eigenvalue and cut, is preserved up to $\kappa$. Batson, Spielman and Srivastava showed that $O(n)$ edges suffice, through a barrier argument that the Marcus–Spielman–Srivastava proof of Kadison–Singer later refined.

- [Weighted Presentation](weighted-presentation.md)
- [Is Cut Approximation](is-cut-approximation.md)
- [Spectral approximation of graphs](spectral-approximation-of-graphs.md)
- [Is Cut Approximation](is-cut-approximation-2.md)
- [Is Spectral Approximation iff pos Semidef](is-spectral-approximation-iff-pos-semide.md)
- [Batson–Spielman–Srivastava, vector form](exists-sparse-reweighting.md)
- [Twice-Ramanujan sparsifiers](exists-twice-ramanujan-sparsifier.md)

## Related topics

- [Graph Laplacians and Cheeger's inequality](../../part-01/graph-laplacians-and-cheeger-s-inequality/README.md): the Laplacians and the Loewner order being approximated.
- [Effective resistance and electrical networks](../../part-01/effective-resistance-and-electrical-networks/README.md): effective resistances are the sampling weights of the randomized sparsifier.
- [Kadison–Singer problem](../../../../Analysis/operator-algebras/kadison-singer-problem/README.md): its barrier bound for mixed characteristic polynomials descends from the barrier potentials of this sparsifier.
- [ε-light vertex sets](../../part-01/light-vertex-sets/README.md): another Loewner-order comparison of a graph Laplacian with the Laplacian of a subgraph.
