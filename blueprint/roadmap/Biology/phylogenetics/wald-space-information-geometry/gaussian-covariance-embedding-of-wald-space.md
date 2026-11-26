# Gaussian covariance embedding of wald space

On a forest $F$ with $N$ labelled leaves, let $Z(t)$ be the stationary Ornstein–Uhlenbeck process along the tree, $Z(t_2) \mid Z(t_1) = z \sim N\bigl(z e^{-\ell_{t_1 t_2}}, 1 - e^{-2\ell_{t_1 t_2}}\bigr)$ with $N(0, 1)$ marginals, independent across components. The leaf values are $N(0, S_F)$ with

$$S_F = \bigl(\exp(-\ell_{uv})\bigr)_{u,v=1}^{N},$$

where $\ell_{uv}$ is the path length between leaves $u$ and $v$ ($\ell_{uu} = 0$, and $\ell_{uv} = \infty$, i.e. $(S_F)_{uv} = 0$, for leaves in different components). Then:

1. $S_F$ is positive definite for every $F$ in wald space;
2. the map $[F] \mapsto S_F$ is injective on wald space, hence embeds it in the cone $\mathcal{S}_N^+$ of positive definite matrices.

Pulling back the affine-invariant metric $\langle X, Y \rangle_S = \tfrac12 \operatorname{tr}(S^{-1} X S^{-1} Y)$, the Fisher metric of zero-mean Gaussians, gives an intrinsic metric on wald space that is finite between any two points.

## Depends on

- [Leaf covariances of the two-state symmetric process on a tree](leaf-covariances-of-the-two-state-symmetric-process.md)
- [Every f-divergence induces the Fisher information metric on tree space](f-divergences-induce-the-fisher-metric-on-tree-space.md)

## Expansion

The Gaussian leaf covariances $e^{-\ell_{uv}}$ match those of the two-state process up to the factor $\tfrac14$, which only rescales the metric. Both parts are proved in the paper's appendix. Intuitively, positive definiteness reflects that no two leaves coincide in wald space, so no leaf value is a deterministic function of the others, and injectivity holds because the tree metric $\ell_{uv} = -\log (S_F)_{uv}$, and hence the forest up to the wald-space equivalence, is recovered from $S_F$. The paper computes geodesics by projecting affine-invariant geodesics of $\mathcal{S}_N^+$ back to wald space.

## Sources

- M. K. Garba et al., *Information geometry for phylogenetic trees*, J. Math. Biol. 82 (2021), 19. <https://doi.org/10.1007/s00285-021-01553-x> (PMCID: PMC7884381) Section 4, Equations (4.1)–(4.2) and Theorem 4.1; Theorem 5.1.
