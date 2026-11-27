# Wilks' theorem, supremum form

Under the hypotheses of [Wilks' theorem (simple null)](tendsto-in-distribution-two-mul-log-like.md), assume moreover that $\hat\theta_n(\omega)$ maximizes the log-likelihood $\ell_n(\theta) = \sum_{i<n} \log p_\theta(X_i(\omega))$ over all $\theta \in \mathbb{R}$, for every $n$ and $\omega$. Then the likelihood-ratio statistic converges in distribution:

$$2\Big(\sup_{\theta \in \mathbb{R}} \ell_n(\theta) - \ell_n(\theta_0)\Big) \to \chi^2_1.$$

## Sources

- S. S. Wilks, *The large-sample distribution of the likelihood ratio for testing composite hypotheses*, Ann. Math. Statist. 9 (1938), 60–62.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Chapter 16.
