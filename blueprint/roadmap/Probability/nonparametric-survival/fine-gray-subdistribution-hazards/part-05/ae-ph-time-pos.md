# Almost sure positivity of the failure time in the proportional subdistribution hazards family

Fix $p \in \mathbb{N}$ and vectors $\beta, x \in \mathbb{R}^p$, write $\langle\beta, x\rangle = \sum_{i=1}^{p} \beta_i x_i$ and $\theta = e^{\langle\beta, x\rangle} > 0$. Let $P_{\beta,x}$ be the [exponential law with rate $\theta$](../part-07/ph-measure.md) on $\mathbb{R}$: the probability measure with density $\theta e^{-\theta\omega}$ for $\omega \ge 0$ and $0$ for $\omega < 0$.

On the sample space $\mathbb{R}$ the failure time $T$ and the failure cause $J$ are

$$
T(\omega) = \begin{cases} \dfrac{\omega}{1-\omega} & \text{if } \omega < 1,\\ 1 & \text{if } \omega \ge 1, \end{cases} \qquad J(\omega) = \begin{cases} \mathrm{true} & \text{if } \omega < 1,\\ \mathrm{false} & \text{if } \omega \ge 1, \end{cases}
$$

where $J = \mathrm{true}$ is the cause of interest and $J = \mathrm{false}$ the competing cause.

For every $p$ and every $\beta, x \in \mathbb{R}^p$, the failure time is positive $P_{\beta,x}$-almost surely: $P_{\beta,x}(T \le 0) = 0$.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509 (for the proportional subdistribution hazards model).
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula (for the model; the latent exponential law, threshold and cause maps, and baseline $(1+t)^{-2}$ here are a construction satisfying (1), not a formula from the paper).
