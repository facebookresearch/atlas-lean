# Largest singular value of a standard Gaussian matrix

Let $X$ be an $n \times d$ matrix with independent $N(0, 1)$ entries and let $\delta \ge 0$. Then

$$\mathbb{P}\big(\sigma_{\max}(X) \ge \sqrt{n}\,(1 + \delta) + \sqrt{d}\big) \le e^{-n\delta^2/2}.$$

The source states the general version for matrices with independent $N(0, \Sigma)$ rows, with
$\gamma_{\max}(\sqrt{\Sigma})$ and $\sqrt{\operatorname{tr}\Sigma / n}$ in place of $1$ and $\sqrt{d/n}$.
The source proof uses
Gordon's comparison inequality and the concentration of Lipschitz functions of Gaussian vectors.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §6.2 (Wishart matrices and their behavior), the case $\Sigma = I$.
- R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, in *Compressed Sensing: Theory and Applications*, Cambridge University Press, 2012, arXiv:1011.3027, Theorem 5.32 and Proposition 5.34, which give the bound with $t = \delta\sqrt{n}$; Corollary 5.35 states the two-sided version.

## Informally uses

- [Concentration of Lipschitz functions of Gaussian variables](../concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/lipschitz-concentration-std-gaussian.md): used in the source proof, since $\sigma_{\max}$ is $1$-Lipschitz in the entries.

## Background

- [Restricted eigenvalue condition](../linear-models-multivariate/lasso-error-bounds-under-restricted-eigenvalues/restricted-eigenvalue.md): random Gaussian designs satisfy it with high probability, by a refinement of this bound.
