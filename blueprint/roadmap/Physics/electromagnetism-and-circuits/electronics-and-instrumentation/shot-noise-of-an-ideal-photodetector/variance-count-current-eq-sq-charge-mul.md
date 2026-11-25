# For a Poisson count, the current variance is $q^2 \lambda / T$

Let $0 \le \eta \le 1$, $P \ge 0$, $h > 0$, $\nu > 0$, $q \ne 0$ and $T > 0$, and let
$\lambda = \eta P / (h \nu)$ be the [mean photoelectron rate](photon-arrival-rate.md). Let $N$ be
an $\mathbb{N}$-valued random variable on a measure space $(\Omega, \mu)$ whose law under $\mu$
is the Poisson distribution with mean $\lambda T$ ($N$ is $\mu$-almost everywhere measurable and
its image measure is that distribution, which forces $\mu$ to be a probability measure). Then the
[window-averaged current](count-current.md) $|q| N / T$ has variance

$$\operatorname{Var}_\mu\!\left[\frac{|q|\, N}{T}\right] = \frac{q^2 \lambda}{T}.$$
