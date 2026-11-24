# The constraint-vector update is the unique maximizer of the expected log-likelihood

Let $I$ be a nonempty finite state set, $\omega > 0$, $R_{ab} > 0$ for all $a \ne b$, $c_b > 0$ and $\omega e_b \ge 0$ for every $b$. Then every $\pi$ with $\pi_b > 0$, $\sum_b \pi_b = 1$ and $\pi \ne \hat\pi$ satisfies

$$\ell(Q_\pi, \pi) < \ell(Q_{\hat\pi}, \hat\pi),$$

where $\ell$ is the [expected log-likelihood](expected-log-lik.md), $Q_\pi$ the [SiPhy matrix](siphy-rate.md) with parameters $\omega, R, \pi$ and $\hat\pi$ the [constraint-vector update](pi-update.md).
