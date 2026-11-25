# Wald instrumental-variable estimand

In a [potential-outcomes model](potential-outcomes.md) with a measure $\mu$, the Wald estimand is

$$W = \frac{\mathbb{E}[Y \mid Z = 1] - \mathbb{E}[Y \mid Z = 0]}{\mathbb{E}[D \mid Z = 1] - \mathbb{E}[D \mid Z = 0]},$$

where $Y$ is the [observed outcome](observed-outcome.md), $D$ the [treatment indicator](treated.md), $\mathbb{E}[\cdot \mid Z = z]$ the [arm mean](arm-mean.md), and $x/0 = 0$.
