# Gaussian covariance embedding of wald space

On a forest $F$ with $N$ labelled leaves, let $Z(t)$ be the stationary Ornstein–Uhlenbeck process along the tree, $Z(t_2) \mid Z(t_1) = z \sim N\bigl(z e^{-\ell_{t_1 t_2}}, 1 - e^{-2\ell_{t_1 t_2}}\bigr)$ with $N(0, 1)$ marginals, independent across components. The leaf values are $N(0, S_F)$ with

$$S_F = \bigl(\exp(-\ell_{uv})\bigr)_{u,v=1}^{N},$$

where $\ell_{uv}$ is the path length between leaves $u$ and $v$ ($\ell_{uu} = 0$, and $\ell_{uv} = \infty$, i.e. $(S_F)_{uv} = 0$, for leaves in different components). Then:

1. $S_F$ is positive definite for every forest $F$ satisfying the three conditions that define [wald space](leaf-covariances-of-the-two-state-symmetric-process.md) (exactly $N$ labelled leaves, no unlabelled vertex of degree at most $2$, and no two leaves joined by a path of zero length);
2. $S_F$ depends only on the class $[F]$ under the BHV and boundary-at-infinity rules, and the map $[F] \mapsto S_F$ is injective on the quotient $\mathcal W_N$, hence embeds wald space in the cone $\mathcal{S}_N^+$ of positive definite matrices.

Pulling back the affine-invariant metric $\langle X, Y \rangle_S = \tfrac12 \operatorname{tr}(S^{-1} X S^{-1} Y)$, the Fisher metric of zero-mean Gaussians, gives an intrinsic metric on wald space that is finite between any two points (Theorem 5.1). This Gaussian Fisher metric is a different metric from the [Fisher metric of the two-state process](f-divergences-induce-the-fisher-metric-on-tree-space.md) on the same forests, which is a comparison here and not a prerequisite.

## Depends on

- [Leaf covariances of the two-state symmetric process on a tree](leaf-covariances-of-the-two-state-symmetric-process.md)

## Expansion

The Gaussian leaf covariances $e^{-\ell_{uv}}$ match those of the two-state process up to the factor $\tfrac14$. Constant scaling of $S$ leaves the affine-invariant metric unchanged, so this factor plays no role in the Gaussian geometry; it does not make the two geometries equal. The Gaussian Fisher metric (4.6) and the two-state Fisher metric differ already for $N = 2$, where both can be written explicitly: they disagree for short edges and converge only as the edge length tends to infinity. Both parts are proved in the paper's appendix. Intuitively, positive definiteness reflects that no two leaves coincide in wald space, so no leaf value is a deterministic function of the others, and injectivity holds because the tree metric $\ell_{uv} = -\log (S_F)_{uv}$, and hence the forest up to the wald-space equivalence, is recovered from $S_F$. The paper approximates geodesics of the induced intrinsic metric by projecting affine-invariant geodesics of $\mathcal{S}_N^+$ back to wald space (Sections 4–5); the algorithm produces approximate geodesics and is not shown to return exact ones.

## Sources

- M. K. Garba et al., *Information geometry for phylogenetic trees*, J. Math. Biol. 82 (2021), 19. <https://doi.org/10.1007/s00285-021-01553-x> (PMCID: PMC7884381) Section 4, Equations (4.1)–(4.2) and Theorem 4.1; Theorem 5.1.
