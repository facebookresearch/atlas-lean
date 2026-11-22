# Local average treatment effect theorem

Let a [potential-outcomes model](potential-outcomes.md) on a probability measure $\mu$ satisfy [independence](independence.md), [exclusion](exclusion.md) and [monotonicity](monotonicity.md), let every potential outcome $Y(z, d)$ be $\mu$-integrable, let $\mu(\{Z = z\}) \ne 0$ for both $z$, and let the [compliers](compliers.md) have nonzero measure (relevance). Then for each $z \in \{0, 1\}$ (Imbens & Angrist 1994, Theorem 1; Angrist, Imbens & Rubin 1996),

$$W = \int \bigl(Y(z, 1) - Y(z, 0)\bigr) \, d\mu(\cdot \mid \text{compliers}),$$

where $W$ is the [Wald estimand](wald-estimand.md): the Wald estimand is the average treatment effect among compliers, and by exclusion the choice of $z$ does not matter.

## Sources

- G. W. Imbens, J. D. Angrist, *Identification and estimation of local average treatment effects*, Econometrica 62 (1994), 467–475, Theorem 1.
- J. D. Angrist, G. W. Imbens, D. B. Rubin, *Identification of causal effects using instrumental variables*, J. Amer. Statist. Assoc. 91 (1996), 444–455.
