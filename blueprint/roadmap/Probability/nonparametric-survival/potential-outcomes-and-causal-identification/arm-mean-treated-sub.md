# First stage: treatment-rate difference equals complier share

Let a [potential-outcomes model](potential-outcomes.md) on a probability measure $\mu$ satisfy [independence](independence.md) and [monotonicity](monotonicity.md), and let $\mu(\{Z = z\}) \ne 0$ for both $z \in \{0, 1\}$. Then (Imbens & Angrist 1994)

$$\mathbb{E}[D \mid Z = 1] - \mathbb{E}[D \mid Z = 0] = \mu(\text{compliers}),$$

where $D$ is the [treatment indicator](treated.md), $\mathbb{E}[\cdot \mid Z = z]$ the [arm mean](arm-mean.md) and the compliers are defined on [their page](compliers.md).

## Sources

- G. W. Imbens, J. D. Angrist, *Identification and estimation of local average treatment effects*, Econometrica 62 (1994), 467–475.
