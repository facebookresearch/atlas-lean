# Expected log-likelihood of the SiPhy matrix

Let $n$ be a real matrix, $\tau, r$ real functions, $\omega > 0$, $R_{ab} > 0$ for all $a \ne b$, and $\pi_b > 0$ for all $b$. Then

$$\ell(Q, \pi) = N \log \omega + \sum_{a \ne b} n_{ab} \log R_{ab} + F(c, \omega e; \pi),$$

where $\ell$ is the [expected log-likelihood](expected-log-lik.md), $Q$ the [SiPhy matrix](siphy-rate.md) with parameters $\omega, R, \pi$, $N$ the [total count](total-count.md), $c$ the [state weights](in-count.md), $e$ the [exchange rates](exit-weight.md) and $F$ the [constraint-vector objective](pi-objective.md).
