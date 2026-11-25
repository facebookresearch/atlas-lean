# Wilks' theorem (simple null)

Under the regularity conditions (R) of [Wald's test](tendsto-in-distribution-wald-statistic.md), with $(\theta, x) \mapsto p_\theta(x)$ jointly measurable in place of the measurability of $p_{\theta_0}$, the log-likelihood-ratio statistic of the consistent root $\hat\theta_n$ of the likelihood equation converges in distribution:

$$2\big(\ell_n(\hat\theta_n) - \ell_n(\theta_0)\big) \to \chi^2_1, \qquad \ell_n(\theta) = \sum_{i=0}^{n-1} \log p_\theta(X_i).$$

## Sources

- S. S. Wilks, *The large-sample distribution of the likelihood ratio for testing composite hypotheses*, Ann. Math. Statist. 9 (1938), 60–62, case of a one-dimensional parameter and a simple null hypothesis.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 16.
