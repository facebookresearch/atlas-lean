# The mean of the marginal estimates

Let $P$ be a probability measure, $X$ a real $N \times M$ matrix, $\beta \in \mathbb{R}^M$, and let $\varepsilon_1, \dots, \varepsilon_N$ be $P$-integrable with $\int \varepsilon_i \, dP = 0$. Then for every marker $j$,

$$\int \hat\beta_j \, dP = \sum_{k=1}^{M} R_{jk} \beta_k, \qquad R_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

where $\hat\beta_j$ is the [marginal estimate](marginal-effect.md) (Zhu and Stephens 2017).

## Sources

- X. Zhu, M. Stephens, *Bayesian large-scale multiple regression with summary statistics from genome-wide association studies*, Ann. Appl. Stat. 11 (2017), 1561–1592.
