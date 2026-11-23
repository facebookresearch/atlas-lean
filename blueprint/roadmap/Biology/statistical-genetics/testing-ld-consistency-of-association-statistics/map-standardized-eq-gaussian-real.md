# Exact law of the standardized DENTIST difference

Let $P$ be a measure on a measurable space $\Omega$ and let $z_i, z_c$ be real functions on $\Omega$ such that the pair $(z_i, z_c)$ has a Gaussian law under $P$, with $\operatorname{Var}(z_i) = \operatorname{Var}(z_c) = 1$, $\operatorname{Cov}(z_i, z_c) = \rho$, $\int z_i \, dP = \rho\lambda$ and $\int z_c \, dP = \lambda$. Let $r$ be a real number with $r^2 < 1$. Then the law of

$$\frac{z_i - r z_c}{\sqrt{1 - r^2}}$$

under $P$ is the normal distribution with mean $m(\rho, r, \lambda)$ ([mean](dentist-mean.md)) and variance $\max(v(\rho, r), 0)$ ([variance](dentist-variance.md)). So the [DENTIST-S statistic](dentist-s.md) is the square of a Gaussian variable: in general a scaled non-central $\chi^2_1$.
