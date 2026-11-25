# Wald consistency of the MLE, almost surely

Let $\Theta$ be a pseudometric space, $K \subseteq \Theta$ compact and $\ell(\theta, x)$ a log-likelihood with $\theta \mapsto \ell(\theta, x)$ continuous on $K$ for every $x$. Assume the uniform law of large numbers: almost surely $\frac1n\sum_{i<n} \ell(\theta, X_i) \to Q(\theta) = \mathbb E\,\ell(\theta, X_0)$ uniformly on $K$; and assume $\theta_0 \in K$ is the unique maximizer of $Q$ on $K$. Then every maximum-likelihood estimator $\hat\theta_n$ on $K$ (maximizing the average log-likelihood over $K$) converges to $\theta_0$ almost surely.
