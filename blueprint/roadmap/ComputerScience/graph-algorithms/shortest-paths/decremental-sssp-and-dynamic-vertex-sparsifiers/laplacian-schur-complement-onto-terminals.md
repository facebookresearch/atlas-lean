# Schur complements of graph Laplacians onto terminal sets and spectral vertex sparsifiers

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and Laplacian $L$, and let $\emptyset \ne T \subsetneq V$ be a set of *terminals*, $N = V \setminus T$. Writing $L$ in block form with respect to $(T, N)$, the *Schur complement* of $L$ onto $T$ is

$$
\mathrm{SC}(L, T) = L_{TT} - L_{TN}\,L_{NN}^{-1}\,L_{NT},
$$

which is well defined since $L_{NN}$ is positive definite. For $\varepsilon \in (0, 1)$, a weighted graph $H$ on vertex set $T$ with Laplacian $L_H$ is a *$(1 \pm \varepsilon)$ spectral vertex sparsifier* of $G$ with respect to $T$ if

$$
(1 - \varepsilon)\,\mathrm{SC}(L, T) \preceq L_H \preceq (1 + \varepsilon)\,\mathrm{SC}(L, T).
$$

## Depends on

- [Weighted Laplacian of a multigraph](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/laplacian.md)

## Sources

- David Durfee, Yu Gao, Gramoz Goranci, Richard Peng, "Fully Dynamic Spectral Vertex Sparsifiers and Applications", STOC (2019), arXiv:1906.10530.
- Rasmus Kyng, Sushant Sachdeva, "Approximate Gaussian Elimination for Laplacians: Fast, Sparse, and Simple", FOCS (2016), arXiv:1605.02353.
