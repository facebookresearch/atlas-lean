# Lasso error bounds under restricted eigenvalues

In sparse linear regression $y = X\theta^* + w$ with more unknowns than observations, the
least-squares loss is never strongly convex, but its curvature is only needed along the cone
$\mathcal{C}(S; \alpha) = \{\Delta : \|\Delta_{S^c}\|_1 \le \alpha \|\Delta_S\|_1\}$ in which the
error of the Lasso lies. The restricted eigenvalue condition asks for a lower bound
$\frac1n \|X\Delta\|_2^2 \ge \kappa \|\Delta\|_2^2$ on that cone, and gives deterministic
$\ell_2$-error bounds of order $\frac{1}{\kappa}\sqrt{s}\,\lambda$ for the regularized and the
constrained Lasso (Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015,
§11.2; Wainwright, *High-Dimensional Statistics*, 2019, §7.3). The restricted eigenvalue condition was introduced, in a slightly different normalisation (their
Assumption RE$(s, c_0)$ divides $\|X\Delta\|_2/\sqrt n$ by $\|\Delta_S\|_2$ rather than by $\|\Delta\|_2$), by Bickel, Ritov and Tsybakov
("Simultaneous analysis of Lasso and Dantzig selector", *Ann. Statist.* 37 (2009) 1705–1732),
who proved bounds of this kind for the Lasso and the Dantzig selector together.

- [The cone $\mathcal{C}(S; \alpha)$](cone.md)
- [Restricted eigenvalue condition](restricted-eigenvalue.md)
- [Lagrangian Lasso objective](lasso-objective.md)
- [$\ell_1$ norm on a support set bounded by the $\ell_2$ norm](sum-abs-le-sqrt-card-mul.md)
- [Basic inequality for the Lagrangian Lasso](lasso-basic-inequality.md)
- [$\ell_2$-error bound for the Lagrangian Lasso](lasso-l2-error-le.md)
- [$\ell_2$-error bound for the constrained Lasso](constrained-lasso-l2-error-le.md)

## Prediction error

- [Slow rate for the Lasso prediction error, constant 3](lasso-prediction-error-le-three.md)
- [Slow rate for the Lasso prediction error](lasso-prediction-error-le-slow.md)
- [Fast rate for the Lasso prediction error](lasso-prediction-error-le-fast.md)

## Related topics

- [Exact recovery by basis pursuit](../exact-recovery-by-basis-pursuit/README.md)
- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md)
- [Sub-exponential variables and Bernstein's inequality](../../concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/README.md)
- [Gauss–Markov covariance minimality](../gauss-markov-covariance-minimality.md)
- [Sparse recovery under the restricted isometry property](../../../Analysis/approximation-theory/sparse-recovery-under-the-restricted-isometry-pr/README.md): the compressed-sensing condition on the design; restricted isometry with $\delta_{2s} < \sqrt2 - 1$ implies the restricted nullspace property, and stable recovery bounds of the same form as the Lasso bounds.
