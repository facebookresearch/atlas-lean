# Method-of-moments estimate from the first n counts

For a real size factor $\sigma$, counts $X_0, X_1, \dots : \Omega \to \mathbb{N}$ and
$n \in \mathbb{N}$, the method-of-moments estimate of $(a, b)$ from the first $n$ counts is

$$
\hat\theta^{\mathrm{mom}}_n(\omega) = \Bigl(\frac{\hat M_n^2}{\hat V_n - \hat M_n},\quad
\frac{\sigma \hat M_n}{\hat V_n - \hat M_n}\Bigr),
$$

the [moment shape](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-shape.md) and
[moment rate](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/mom-rate.md) at the
[sample mean](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/sample-mean.md)
$\hat M_n = n^{-1} \sum_{i < n} X_i(\omega)$ and the
[biased sample variance](../../bayesian-statistics/gamma-poisson-counts-and-empirical-bayes-shrinka/sample-var.md)
$\hat V_n = n^{-1} \sum_{i < n} X_i(\omega)^2 - \hat M_n^2$. With the convention $x / 0 = 0$ both
coordinates are $0$ when $\hat V_n = \hat M_n$, in particular for $n = 0$.
