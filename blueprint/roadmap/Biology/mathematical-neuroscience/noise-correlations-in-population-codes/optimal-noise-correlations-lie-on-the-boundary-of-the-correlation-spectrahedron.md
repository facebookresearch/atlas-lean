# Optimal noise correlations lie on the boundary of the correlation spectrahedron

Fix tuning-curve derivatives $\mu' \in \mathbb{R}^n$ and noise variances $\sigma_1^2, \dots, \sigma_n^2 > 0$. The set of admissible noise covariance matrices with these variances,

$$\mathcal{S} = \{\Sigma \in \mathbb{R}^{n\times n} : \Sigma = \Sigma^{\top} \succeq 0,\ \Sigma_{ii} = \sigma_i^2\},$$

is a compact convex set (a **spectrahedron**, the slice of the positive semidefinite cone by the diagonal constraints), parametrized by the $n(n-1)/2$ noise correlations. Let $\mathcal{R} \subseteq \mathcal{S}$ be any compact convex region of allowed correlations (for example $\mathcal{S}$ itself, or $\mathcal{S}$ intersected with a norm ball on the correlations) on which the information measure is finite.

**Theorem.** The linear Fisher information $I_F(\Sigma) = \mu'^{\top}\Sigma^{-1}\mu'$ is a convex function of $\Sigma$ on the positive definite cone. Consequently its maximum over $\mathcal{R}$ is attained at a boundary point of $\mathcal{R}$, and indeed at an extreme point of $\mathcal{R}$. The same holds for the optimal-linear-estimator information and for Gaussian mutual information.

For $\mathcal{R} = \mathcal{S}$ the boundary consists of singular covariance matrices, so information-optimal correlation structures are degenerate: some linear combination of the responses has zero noise variance.

## Expansion

Convexity of the matrix-fractional function: for $\Sigma \succ 0$, $x^{\top}\Sigma^{-1}x = \sup_{y}\,(2y^{\top}x - y^{\top}\Sigma y)$ is a supremum of functions affine in $\Sigma$, hence convex. A convex function on a compact convex set attains its maximum at an extreme point (any point is a convex combination of extreme points, and $f$ of a convex combination is at most the corresponding combination of values). The theorem holds for any additional convex constraint, which matters biologically because circuit mechanisms such as shared input may bound individual correlations. For larger populations the optimum is typically far from the sign-rule direction and can be attained by many disjoint correlation structures.

## Sources

- Y. Hu, J. Zylberberg, E. Shea-Brown, "The sign rule and beyond: boundary effects, flexibility, and noise correlations in neural population codes", PLoS Computational Biology 10(2) (2014) e1003469, Theorem 2 and Methods "Proof of Theorem 2: optima lie on boundaries", <https://doi.org/10.1371/journal.pcbi.1003469>, PMCID PMC3937411.
