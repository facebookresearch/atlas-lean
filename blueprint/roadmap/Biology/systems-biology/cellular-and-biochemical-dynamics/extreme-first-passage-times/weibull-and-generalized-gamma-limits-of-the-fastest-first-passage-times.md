# Weibull and generalized-gamma limits of the fastest first passage times

**Setting.** Let $\tau_1, \tau_2, \dots$ be i.i.d. first passage times of $N$ independent diffusive searchers to a target, and let $T_{k,N}$ be the $k$-th smallest of $\tau_1, \dots, \tau_N$ ($T_N = T_{1,N}$ is the **extreme first passage time**).

**Theorem (power-law short-time regime).** Suppose that for some $A > 0$ and $p > 0$

$$\mathbb P(\tau_1 \le t) \sim A t^p \qquad (t \to 0^+).$$

Then $(AN)^{1/p}T_N \to \mathrm{Weibull}(1, p)$ in distribution, and more generally $(AN)^{1/p}T_{k,N}$ converges to a generalized gamma law $\mathrm{gen}\Gamma(1, p, k)$. If $\mathbb E[T_N] < \infty$ for some $N$, then for every $m > 0$

$$\mathbb E[(T_{k,N})^m] \sim \frac{\Gamma(k + m/p)/\Gamma(k)}{(AN)^{m/p}} \qquad (N \to \infty),$$

in particular $\mathbb E[T_N] \sim \Gamma(1 + 1/p)(AN)^{-1/p}$.

**Proposition (slow-escape regime).** If instead $\lambda\tau \to \mathrm{Exp}(1)$ as a small parameter $\varepsilon \to 0$ (narrow escape, deep potential well), then for fixed $N$ the order statistics satisfy $\lambda T_{k,N} \to$ the $k$-th order statistic of $N$ independent unit exponentials, so $\mathbb E[T_N] \approx 1/(N\lambda)$.

**Competition.** In the Gaussian short-time case $\mathbb P(\tau_1 \le t) \sim At^pe^{-C/t}$ the fastest time obeys a Gumbel law with $\mathbb E[T_N] \sim C/\ln N$. Which regime describes a given system depends on whether $N$ is large compared to the ratio of the slow mean escape time to the fast diffusive timescale: the fastest searcher ignores the slow exponential escape and instead follows rare direct trajectories.

## Proof sketch

$\mathbb P(T_N > t) = (1 - \mathbb P(\tau_1 \le t))^N$, so at the scale $t = s(AN)^{-1/p}$ one gets $(1 - As^p/N)^N \to e^{-s^p}$, the Weibull survival function; the $k$-th order statistic follows from the Poisson approximation of the number of $\tau_n \le t$. Moment convergence needs only finiteness of one moment because the large-$N$ minimum lives where the short-time asymptotics applies. In the slow regime the extreme time does not depend on the initial searcher distribution, but in the fast regime it depends on it critically: an initial density that is positive up to the target gives a power law (e.g. $p = 1/2$ in one dimension, so $\mathbb E[T_N] \propto N^{-2}$), whereas searchers starting at a positive distance give the Gumbel case with $\mathbb E[T_N] \propto 1/\ln N$.

## Sources

- Jacob B. Madrid and Sean D. Lawley, "Competition between slow and fast regimes for extreme first passage times of diffusion *", *Journal of Physics A: Mathematical and Theoretical* 53 (2020), 335002, <https://doi.org/10.1088/1751-8121/ab96ed>. Preprint version: arXiv:2004.05414 (2020), Proposition 1 (Section 2), Theorems 2, 3, 5, 6 and 7–8 (Section 3), Section 4, <https://doi.org/10.48550/arXiv.2004.05414>.
