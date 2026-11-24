# For a Poisson count, the mean current is responsivity times power

Let $0 \le \eta \le 1$, $P \ge 0$, $h > 0$, $\nu > 0$, $q \ne 0$ and $T > 0$, and let
$\lambda = \eta P / (h \nu)$ be the [mean photoelectron rate](photon-arrival-rate.md). Let $N$ be
an $\mathbb{N}$-valued random variable on a measure space $(\Omega, \mu)$ whose law under $\mu$
is the Poisson distribution with mean $\lambda T$, $\mu(N = k) = e^{-\lambda T} (\lambda T)^k / k!$
($N$ is $\mu$-almost everywhere measurable and its image measure is that distribution, which forces
$\mu$ to be a probability measure). Then the mean of the
[window-averaged current](count-current.md) $|q| N / T$ is the [responsivity](responsivity.md)
times the power:

$$\mathbb{E}_\mu\!\left[\frac{|q|\, N}{T}\right] = R P = \frac{\eta\, |q|}{h \nu}\, P.$$
