# Strong consistency of maximum likelihood with an upper semicontinuous criterion

For a log-likelihood $\ell_\theta(x)$ and observations $X_0, X_1, \dots$ on a measure space with measure $P$ (expectations are integrals against $P$), write $\bar\ell_n(\theta) = \frac1n\sum_{i<n}\ell_\theta(X_i)$ for the average log-likelihood and $Q(\theta) = \mathbb{E}[\ell_\theta(X_0)]$ for the population criterion. Let $K$ be a compact subset of a pseudometric parameter space, $Q$ upper semicontinuous on $K$ with unique maximizer $\theta_0 \in K$, and assume the uniform law of large numbers on $K$. Then every maximum-likelihood estimator on $K$ converges to $\theta_0$ almost surely.

## Sources

- A. Wald, "Note on the consistency of the maximum likelihood estimate", *Annals of Mathematical Statistics* 20 (1949), 595–601.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Theorem 5.7.
