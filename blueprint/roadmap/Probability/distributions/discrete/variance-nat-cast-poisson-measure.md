# Variance of the Poisson distribution

Let $r \ge 0$ and let $\mathrm{Po}(r)$ be the Poisson law on $\mathbb{N}$ with mean $r$, $\mathrm{Po}(r)(\{n\}) = e^{-r} r^n / n!$. The variance of the real random variable $n \mapsto n$ under $\mathrm{Po}(r)$ is

$$\mathrm{Var}_{\mathrm{Po}(r)}[N] = \int_{\mathbb{N}} \Big(n - \int m \, d\mathrm{Po}(r)(m)\Big)^2 d\mathrm{Po}(r)(n) = r.$$
