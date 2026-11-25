# Likelihood ratio on the boundary

Consider the one-sided parameter space $\theta \in [0, \infty)$ with true value $\theta_0 = 0$. Assume the hypotheses of [Wilks' theorem (simple null)](tendsto-in-distribution-two-mul-log-like.md) at $\theta_0 = 0$: the family is defined and regular on a ball about $0$ (so $0$ is interior to the domain of the family, though not to the parameter space), and $\hat\theta_n$ is a consistent root of the likelihood equation. Then the statistic of the estimator projected onto $[0, \infty)$ converges in distribution to a mixture:

$$2\big(\ell_n(\max(\hat\theta_n, 0)) - \ell_n(0)\big) \to \tfrac12 \delta_0 + \tfrac12 \chi^2_1.$$

The projection $\max(\hat\theta_n, 0)$ is the restricted maximizer when, for example, $\ell_n$ is concave; that is not assumed.

## Sources

- H. Chernoff, *On the distribution of the likelihood ratio*, Ann. Math. Statist. 25 (1954), 573–578.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 16.
