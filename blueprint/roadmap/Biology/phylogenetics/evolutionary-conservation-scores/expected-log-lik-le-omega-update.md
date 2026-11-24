# The rate update maximizes the expected log-likelihood

Let $R_{ab} > 0$ for all $a \ne b$, $\pi_b > 0$ for all $b$, $N > 0$ and $\sum_b e_b \pi_b > 0$, where $N$ is the [total count](total-count.md) and $e$ the [exchange rates](exit-weight.md). Then for every $\omega > 0$,

$$\ell(Q_\omega, \pi) \le \ell(Q_{\hat\omega}, \pi),$$

where $\ell$ is the [expected log-likelihood](expected-log-lik.md), $Q_\omega$ the [SiPhy matrix](siphy-rate.md) with rate $\omega$ and $\hat\omega$ the [rate update](omega-update.md).
