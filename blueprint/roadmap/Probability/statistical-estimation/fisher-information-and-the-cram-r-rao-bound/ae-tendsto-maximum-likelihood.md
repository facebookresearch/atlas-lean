# Wald's consistency theorem for maximum likelihood

Let $\Theta$ be a compact metric space, $(\mathcal{X}, \nu)$ a measure space and $p_\theta : \mathcal{X} \to (0, \infty)$, $\theta \in \Theta$, positive functions, measurable in $x$, continuous in $\theta$, with $\int p_\theta\, d\nu = 1$. Let $\theta_0 \in \Theta$ and assume:

- identifiability: $p_\theta = p_{\theta_0}$ $\nu$-almost everywhere only for $\theta = \theta_0$;
- an envelope: $\log p_\theta(x) - \log p_{\theta_0}(x) \le K(x)$ for all $\theta, x$, with $K$ integrable under $P_{\theta_0} = p_{\theta_0} \cdot \nu$.

Let $X_0, X_1, \dots$ be independent random variables with law $P_{\theta_0}$ on a probability space $(\Omega, P)$, and let $\hat\theta_n(\omega)$ maximize the log-likelihood $\theta \mapsto \sum_{i<n} \log p_\theta(X_i(\omega))$ over $\Theta$ for every $n$ and $\omega$. Then $\hat\theta_n \to \theta_0$ $P$-almost surely.

## Sources

- A. Wald, *Note on the consistency of the maximum likelihood estimate*, Ann. Math. Statist. 20 (1949), 595–601.
- T. S. Ferguson, *A Course in Large Sample Theory*, Chapman & Hall, 1996, Theorem 17.
