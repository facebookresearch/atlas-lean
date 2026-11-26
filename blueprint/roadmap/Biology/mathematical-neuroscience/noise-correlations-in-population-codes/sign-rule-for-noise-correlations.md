# Sign rule for noise correlations

Consider $n$ neurons whose mean responses to a scalar stimulus $s$ are given by differentiable tuning curves $\mu_i(s)$, with conditional noise covariance $\Sigma$ at a fixed stimulus. Hold the variances $\Sigma_{ii} = \sigma_i^2 > 0$ fixed and vary only the off-diagonal entries $\Sigma_{ij} = \rho_{ij}\sigma_i\sigma_j$, keeping $\Sigma$ positive definite. The **linear Fisher information** is

$$I_F(\Sigma) = \mu'(s)^{\top} \Sigma^{-1} \mu'(s).$$

Assume $\mu_i'(s) \neq 0$ for all $i$ and define the local **signal correlation** of a pair as $\operatorname{sgn}(\mu_i'(s)\mu_j'(s))$. Let $\Sigma_0 = \operatorname{diag}(\sigma_1^2,\dots,\sigma_n^2)$ (independent, trial-shuffled noise).

**Theorem (sign rule).** Let $C$ be a symmetric matrix with zero diagonal, $C \ne 0$, such that every nonzero off-diagonal entry satisfies $\operatorname{sgn}(C_{ij}) = -\operatorname{sgn}(\mu_i'\mu_j')$ (noise correlations opposite in sign to signal correlations). Then $I_F(\Sigma_0 + tC) > I_F(\Sigma_0)$ for every $t > 0$ with $\Sigma_0 + tC$ positive definite. If instead every nonzero $C_{ij}$ has the same sign as $\mu_i'\mu_j'$, then $I_F(\Sigma_0 + tC) < I_F(\Sigma_0)$ for all sufficiently small $t > 0$.

The same statement holds for the accuracy of the optimal linear estimator and for Gaussian mutual information, with signal correlations defined from the covariance of the tuning curves across stimuli.

## Depends on

- [Optimal noise correlations lie on the boundary of the correlation spectrahedron](optimal-noise-correlations-lie-on-the-boundary-of-the-correlation-spectrahedron.md)

## Expansion

Differentiating $\Sigma \mapsto \mu'^{\top}\Sigma^{-1}\mu'$ in the direction $C$ gives $-\mu'^{\top}\Sigma^{-1} C \Sigma^{-1}\mu'$. At $\Sigma_0$ this equals

$$-\sum_{i \ne j} C_{ij}\,\frac{\mu_i'\mu_j'}{\sigma_i^2\sigma_j^2},$$

which is strictly positive under the sign rule and strictly negative under the anti-sign rule; the gradient at independence points along $-\mu_i'\mu_j'/(\sigma_i^2\sigma_j^2)$. Because $I_F$ is convex in $\Sigma$ on the positive definite cone, $I_F(\Sigma_0 + tC) \ge I_F(\Sigma_0) + t\, D I_F(\Sigma_0)[C]$, so the improvement under the sign rule persists along the whole ray, not only to first order. Convexity also explains the asymmetry: along an anti-sign-rule ray information first decreases but may later increase above the independent value, so the sign rule is sufficient but not necessary for correlations to help.

## Sources

- Y. Hu, J. Zylberberg, E. Shea-Brown, "The sign rule and beyond: boundary effects, flexibility, and noise correlations in neural population codes", PLoS Computational Biology 10(2) (2014) e1003469, Theorem 1 and Methods "Proof of Theorem 1: the generality of the sign rule", <https://doi.org/10.1371/journal.pcbi.1003469>, PMCID PMC3937411.
