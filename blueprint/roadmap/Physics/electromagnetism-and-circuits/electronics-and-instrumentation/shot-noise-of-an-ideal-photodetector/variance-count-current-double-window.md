# Doubling the counting window halves the current variance

Let $0 \le \eta \le 1$, $P \ge 0$, $h > 0$, $\nu > 0$, $q \ne 0$ and $T > 0$, and let
$\lambda = \eta P / (h \nu)$ be the [mean photoelectron rate](photon-arrival-rate.md). Let $N_1$
and $N_2$ be $\mathbb{N}$-valued random variables on one measure space $(\Omega, \mu)$ whose laws
under $\mu$ are the Poisson distributions with means $\lambda T$ and $2 \lambda T$ ($\mu$-almost
everywhere measurable with these image measures, which forces $\mu$ to be a probability measure;
no independence of $N_1$ and $N_2$ is assumed). Then the
[window-averaged current](count-current.md) over the window $2T$ has half the variance of the one
over the window $T$:

$$\operatorname{Var}_\mu\!\left[\frac{|q|\, N_2}{2T}\right]
= \frac{1}{2} \operatorname{Var}_\mu\!\left[\frac{|q|\, N_1}{T}\right].$$
