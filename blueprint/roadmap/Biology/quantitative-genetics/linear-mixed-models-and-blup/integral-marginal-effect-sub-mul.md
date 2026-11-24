# The raw residual-product second moment of the marginal estimates

Let $P$ be a measure, $X$ a real $N \times M$ matrix, $\beta \in \mathbb{R}^M$ and $\sigma^2 \in \mathbb{R}$, and let $\varepsilon_1, \dots, \varepsilon_N$ be such that every product $\varepsilon_i \varepsilon_{i'}$ is $P$-integrable with $\int \varepsilon_i \varepsilon_{i'} \, dP = \sigma^2$ if $i = i'$ and $0$ otherwise. Then for all markers $j, k$,

$$\int \bigl(\hat\beta_j - (R\beta)_j\bigr)\bigl(\hat\beta_k - (R\beta)_k\bigr) \, dP = \frac{\sigma^2}{N}\, R_{jk},$$

where $\hat\beta$ is the [marginal estimate](marginal-effect.md) and $R_{jk} = \frac1N \sum_i X_{ij} X_{ik}$ (Zhu and Stephens 2017). Neither a probability measure nor mean-zero noise is assumed, so this is a raw second moment; with both, it is the covariance of the marginal estimates.

## Sources

- X. Zhu, M. Stephens, *Bayesian large-scale multiple regression with summary statistics from genome-wide association studies*, Ann. Appl. Stat. 11 (2017), 1561–1592.
