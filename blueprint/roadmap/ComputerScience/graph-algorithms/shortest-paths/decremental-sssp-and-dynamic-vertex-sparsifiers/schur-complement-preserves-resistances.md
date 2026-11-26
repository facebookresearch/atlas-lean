# Laplacian Schur complements are Laplacians and preserve terminal effective resistances

In the setting of the Schur complement onto terminals, $\mathrm{SC}(L, T)$ is the Laplacian of a connected weighted graph on $T$, and for all $u, v \in T$,

$$
R_{\mathrm{eff}}^{G}(u, v) = R_{\mathrm{eff}}^{\mathrm{SC}(L, T)}(u, v), \qquad x^\top \mathrm{SC}(L, T)\, x = \min_{y \in \mathbb{R}^{N}} (x, y)^\top L\, (x, y) \ \text{ for all } x \in \mathbb{R}^{T}.
$$

Hence a $(1 \pm \varepsilon)$ spectral vertex sparsifier approximates all terminal effective resistances within a factor $1 \pm O(\varepsilon)$, as well as electrical energies of demands supported on $T$.

## Proof sketch

Eliminating one non-terminal vertex $v$ by Gaussian elimination replaces its star by a weighted clique on its neighbours (edge $\{a, b\}$ of weight $w_{av}w_{bv}/\deg_w(v)$), which is again a Laplacian of a connected graph; iterating over $N$ gives $\mathrm{SC}(L, T)$. The variational identity follows by minimizing the quadratic form over $y$, whose minimizer is $y = -L_{NN}^{-1}L_{NT}x$, i.e. harmonic extension. Effective resistance between terminals is the inverse of the minimal energy of a unit potential difference, so it is determined by the quadratic form on $T$, and Loewner bounds transfer to resistances by inversion.

## Depends on

- [Schur complements of graph Laplacians onto terminal sets and spectral vertex sparsifiers](laplacian-schur-complement-onto-terminals.md)

## Proof depends on

- [Effective resistance](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance.md)
- [Schur complement of a positive-definite block matrix is positive definite](../../../../LinearAlgebra/not-yet-classified/schur-strict-positivity/schur-complement-pos-def.md)

## Sources

- Rasmus Kyng, Sushant Sachdeva, "Approximate Gaussian Elimination for Laplacians: Fast, Sparse, and Simple", FOCS (2016), arXiv:1605.02353.
- David Durfee, Yu Gao, Gramoz Goranci, Richard Peng, "Fully Dynamic Spectral Vertex Sparsifiers and Applications", STOC (2019), arXiv:1906.10530.
