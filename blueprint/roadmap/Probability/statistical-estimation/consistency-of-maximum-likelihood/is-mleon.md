# Maximum likelihood estimator on a set

For a log-likelihood $\ell(\theta, x)$, observations $X_0, X_1, \dots$ and a set $K$ of parameters, an estimator sequence $\hat\theta_n$ is a maximum likelihood estimator on $K$ when, for every $n$ and every outcome $\omega$, $\hat\theta_n(\omega) \in K$ and

$$\frac1n\sum_{i<n}\ell(\theta, X_i(\omega)) \le \frac1n\sum_{i<n}\ell(\hat\theta_n(\omega), X_i(\omega)) \quad\text{for all } \theta \in K,$$

where the average is $0$ when $n = 0$, by the convention $x/0 = 0$.
