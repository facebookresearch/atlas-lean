# Net decay rate of the latent reservoir under suppressive therapy

Under fully suppressive therapy new infections stop, and the expected number $L(t)$ of latently infected cells evolves by proliferation at rate $p \ge 0$, reactivation at rate $a \ge 0$ and death at rate $d_L \ge 0$:

$$\dot L = p L - a L - d_L L, \qquad L(t) = L_0\, e^{-\delta t}, \qquad \delta = d_L + a - p,$$

with half-life $t_{1/2} = \ln 2 / \delta$ when $\delta > 0$. For interventions acting on one rate with the others fixed:

1. multiplying the reactivation rate by $\varphi \ge 1$ (a latency-reversing agent) raises the decay rate to $\delta + (\varphi - 1) a$;
2. reducing proliferation by a fraction $\theta \in [0, 1]$ (an antiproliferative therapy) raises it to $\delta + \theta p$.

Hence the half-life is halved exactly when $\varphi = 1 + \delta/a$, or when $\theta = \delta/p$. Whenever $p \gg a$, a small fractional reduction of proliferation shortens the half-life as much as a large multiplicative increase of reactivation.

## Depends on

- [Basic viral dynamics model and its within-host basic reproductive number](basic-viral-dynamics-model-and-its-reproductive-number.md)

## Proof depends on

- [Uniqueness of the first-order solution](../../../../Chemistry/chemical-kinetics/rate-laws/first-order-sol-unique.md)
- [Half-life of a first-order reaction](../../../../Chemistry/chemical-kinetics/rate-laws/first-order-sol-half-life.md)

## Proof sketch

With $\beta = 0$ the latent compartment decouples from target cells and virus, so its dynamics are linear; adding reactivated cells that revert to latency only changes the effective value of $a$. Doubling $\delta$ halves $t_{1/2}$, which gives the two thresholds. For the HIV reservoir in resting memory CD4+ T cells, the observed half-life is about 44 months ($\delta \approx 5.2 \times 10^{-4}$ per day), while measured turnover gives $p \approx 0.015$ and $d_L \approx 0.0155$ per day and the rebound timing gives $a \approx 5.7 \times 10^{-5}$ per day. With these values the reactivation rate must rise about tenfold, but proliferation need fall only a few percent, to halve the half-life. Because $\delta$ is a small difference of two large rates, such predictions are very sensitive to the poorly known split of $\delta$ into $d_L$, $a$ and $p$. Whether cure occurs is a stochastic question, namely whether any remaining latent cell reactivates and restarts infection, which this expected-value equation does not answer.

## Sources

- A. L. Hill, D. I. S. Rosenbloom, M. A. Nowak and R. F. Siliciano, "Insight into treatment of HIV infection from viral dynamics models", Immunological Reviews 285 (2018), Section 3.1 (Equation 6, Figure 7), <https://doi.org/10.1111/imr.12698>, PMCID: PMC6155466.
