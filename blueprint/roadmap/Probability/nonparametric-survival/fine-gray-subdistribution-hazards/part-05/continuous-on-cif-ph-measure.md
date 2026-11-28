# Continuity of the cumulative incidence on a compact interval in the proportional subdistribution hazards family

Fix $p \in \mathbb{N}$ and vectors $\beta, x \in \mathbb{R}^p$, write $\langle\beta, x\rangle = \sum_{i=1}^{p} \beta_i x_i$ and $\theta = e^{\langle\beta, x\rangle} > 0$. Let $P_{\beta,x}$ be the [exponential law with rate $\theta$](../part-07/ph-measure.md) on $\mathbb{R}$: the probability measure with density $\theta e^{-\theta\omega}$ for $\omega \ge 0$ and $0$ for $\omega < 0$.

On the sample space $\mathbb{R}$ the failure time $T$ and the failure cause $J$ are

$$
T(\omega) = \begin{cases} \dfrac{\omega}{1-\omega} & \text{if } \omega < 1,\\ 1 & \text{if } \omega \ge 1, \end{cases} \qquad J(\omega) = \begin{cases} \mathrm{true} & \text{if } \omega < 1,\\ \mathrm{false} & \text{if } \omega \ge 1, \end{cases}
$$

where $J = \mathrm{true}$ is the cause of interest and $J = \mathrm{false}$ the competing cause.

The cumulative incidence of the cause of interest is $F(t; x) = P_{\beta,x}(T \le t,\ J = \mathrm{true})$, as in the [cumulative incidence function](../part-01/cif.md).

For every $p$, every $\beta, x \in \mathbb{R}^p$ and every $t \in \mathbb{R}$, the function $s \mapsto F(s; x)$ is continuous on the closed interval $[0, t]$ (which is empty when $t < 0$).

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509 (for the proportional subdistribution hazards model).
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula (for the model; the latent exponential law, threshold and cause maps, and baseline $(1+t)^{-2}$ here are a construction satisfying (1), not a formula from the paper).
