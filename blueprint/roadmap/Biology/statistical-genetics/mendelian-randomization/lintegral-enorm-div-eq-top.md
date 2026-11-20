# Ratio with a Gaussian denominator has infinite first moment

Let $\mu$ be a probability measure on a measurable space $\Omega$, let $m \in \mathbb{R}$ and $v > 0$, and let $N, D$ be real random variables such that $D$ has law $N(m, v)$ under $\mu$, $N$ is $\mu$-almost everywhere measurable, $N$ and $D$ are independent under $\mu$, and $N$ is not $\mu$-almost everywhere $0$. Then (a classical fact, recalled in the weak-instrument analysis of Burgess & Thompson 2011)

$$\int \Bigl|\frac{N}{D}\Bigr| \, d\mu = \infty,$$

with the convention $x/0 = 0$. Applied to the ratio estimator $\hat\beta_Y / \hat\beta_X$ with a normally distributed SNP–exposure estimate, it shows that this estimator has no mean.

## Sources

- S. Burgess, S. G. Thompson, *Bias in causal estimates from Mendelian randomization studies with weak instruments*, Stat. Med. 30 (2011), 1312–1323.
