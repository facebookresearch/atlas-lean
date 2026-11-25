# Gamma–Poisson conjugacy, posterior predictive

Let $a, b > 0$ and $k, j \in \mathbb{N}$, and let $\Gamma(a, b)$ be the gamma law with shape $a$ and rate $b$.
Then

$$\frac{\displaystyle\int e^{-r} \frac{r^k}{k!}\, e^{-r} \frac{r^j}{j!}\, d\Gamma(a, b)(r)}{p_{\Gamma(a, b)}(k)} = \mathrm{NB}\Bigl(j; a + k, \frac{a + k}{b + 1}\Bigr),$$

where $p_{\Gamma(a, b)}$ is the [mixed Poisson mass](../mixed-poisson/poisson-mixture-real.md) and $\mathrm{NB}$ the
[negative binomial mass](../negative-binomial/neg-binomial-real.md) with given size and mean. With prior
$\Lambda \sim \Gamma(a, b)$ and counts $N, N'$ independent $\operatorname{Poisson}(\Lambda)$ given
$\Lambda$, the left side is $P(N' = j \mid N = k)$.
