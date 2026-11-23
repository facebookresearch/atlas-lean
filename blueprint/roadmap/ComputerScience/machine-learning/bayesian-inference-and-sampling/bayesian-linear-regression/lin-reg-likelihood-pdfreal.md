# The linear regression likelihood density

For $\sigma^2 \ge 0$, $x, y \in \mathbb{R}^n$
and $w \in \mathbb{R}$, it is the real number $\prod_i \varphi(y_i; w x_i, \sigma^2)$, where
$\varphi(t; \mu, \tau) = (2\pi\tau)^{-1/2} e^{-(t - \mu)^2 / (2\tau)}$ is the Gaussian density
with mean $\mu$ and variance $\tau$ at $t$, read as $0$ when $\tau = 0$. For $\sigma^2 \ne 0$ it
is the Lebesgue density of the responses $y$ given the weight $w$, independent with
$y_i \sim \mathcal{N}(w x_i, \sigma^2)$. With no data ($n = 0$) it is the empty product $1$, the
density of the unit mass on the single empty response. For $\sigma^2 = 0$ and $n > 0$ the
responses are deterministic and have no density, and this formula is $0$.
