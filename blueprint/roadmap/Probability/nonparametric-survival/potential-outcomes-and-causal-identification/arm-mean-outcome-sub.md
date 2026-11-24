# Reduced form: outcome difference is the complier-weighted effect

Let a [potential-outcomes model](potential-outcomes.md) on a probability measure $\mu$ satisfy [independence](independence.md), [exclusion](exclusion.md) and [monotonicity](monotonicity.md), let every potential outcome $Y(z, d)$ be $\mu$-integrable, and let $\mu(\{Z = z\}) \ne 0$ for both $z$. Then for each $z \in \{0, 1\}$ (Imbens & Angrist 1994),

$$\mathbb{E}[Y \mid Z = 1] - \mathbb{E}[Y \mid Z = 0] = \int_{\text{compliers}} \bigl(Y(z, 1) - Y(z, 0)\bigr) \, d\mu,$$

where $Y$ is the [observed outcome](observed-outcome.md) and $\mathbb{E}[\cdot \mid Z = z]$ the [arm mean](arm-mean.md).

## Sources

- G. W. Imbens, J. D. Angrist, *Identification and estimation of local average treatment effects*, Econometrica 62 (1994), 467–475.
