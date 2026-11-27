# Laplacian Schur complements are Laplacians and preserve terminal effective resistances

In the setting of the Schur complement onto terminals, $\mathrm{SC}(L, T)$ is the Laplacian of a connected weighted graph on $T$, and for all $u, v \in T$,

$$
R_{\mathrm{eff}}^{G}(u, v) = R_{\mathrm{eff}}^{\mathrm{SC}(L, T)}(u, v), \qquad x^\top \mathrm{SC}(L, T)\, x = \min_{y \in \mathbb{R}^{N}} (x, y)^\top L\, (x, y) \ \text{ for all } x \in \mathbb{R}^{T}.
$$

Hence, for $0 < \varepsilon < 1$, a $(1 \pm \varepsilon)$ spectral vertex sparsifier $H$ satisfies $\frac{1}{1+\varepsilon} R_{\mathrm{eff}}^{G}(u, v) \le R_{\mathrm{eff}}^{H}(u, v) \le \frac{1}{1-\varepsilon} R_{\mathrm{eff}}^{G}(u, v)$ for all $u, v \in T$, and the same two factors bound the electrical energy in $H$ of every demand on $T$ with total zero against its energy in $G$.

## Proof sketch

Eliminating one non-terminal vertex $v$ by Gaussian elimination replaces its star by a weighted clique on its neighbours (edge $\{a, b\}$ of weight $w_{av}w_{bv}/\deg_w(v)$), which is again a Laplacian of a connected graph; iterating over $N$ gives $\mathrm{SC}(L, T)$. The variational identity follows by minimizing the quadratic form over $y$, whose minimizer is $y = -L_{NN}^{-1}L_{NT}x$, i.e. harmonic extension. Connectivity follows by grounding: deleting the row and column of one terminal $t_0$ from $L$ leaves a positive-definite matrix, since $G$ is connected, and its Schur complement onto $T \setminus \{t_0\}$, which is $\mathrm{SC}(L, T)$ with the row and column of $t_0$ deleted, is positive definite by the block-matrix lemma, so the kernel of $\mathrm{SC}(L, T)$ is spanned by the all-ones vector. Effective resistance between terminals is the inverse of the minimal energy of a unit potential difference, so it is determined by the quadratic form on $T$. Finally, $(1-\varepsilon)\mathrm{SC}(L, T) \preceq L_H \preceq (1+\varepsilon)\mathrm{SC}(L, T)$ with $\varepsilon < 1$ forces both matrices to have the same kernel, and inverting on its complement reverses the bounds, $\frac{1}{1+\varepsilon}\mathrm{SC}(L, T)^{\dagger} \preceq L_H^{\dagger} \preceq \frac{1}{1-\varepsilon}\mathrm{SC}(L, T)^{\dagger}$, which gives the resistance and energy bounds.

## Depends on

- [Schur complements of graph Laplacians onto terminal sets and spectral vertex sparsifiers](laplacian-schur-complement-onto-terminals.md)
- [Effective resistance](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance.md)

## Proof depends on

- [Schur complement of a positive-definite block matrix is positive definite](../../../../LinearAlgebra/not-yet-classified/schur-strict-positivity/schur-complement-pos-def.md)

## Sources

- Rasmus Kyng, Sushant Sachdeva, "Approximate Gaussian Elimination for Laplacians: Fast, Sparse, and Simple", FOCS (2016), arXiv:1605.02353.
- David Durfee, Yu Gao, Gramoz Goranci, Richard Peng, "Fully Dynamic Spectral Vertex Sparsifiers and Applications", STOC (2019), arXiv:1906.10530.
