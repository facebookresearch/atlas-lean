# Unrestricted algebraic identity behind the LATE theorem

Let a [potential-outcomes model](potential-outcomes.md) on a probability measure $\mu$ satisfy [independence](independence.md), [exclusion](exclusion.md) and [monotonicity](monotonicity.md), let every potential outcome $Y(z, d)$ be $\mu$-integrable, and let $\mu(\{Z = z\}) \ne 0$ for both $z$. Then for each $z \in \{0, 1\}$,

$$W = \int \bigl(Y(z, 1) - Y(z, 0)\bigr) \, d\mu(\cdot \mid \text{compliers}),$$

where $W$ is the [Wald estimand](wald-estimand.md) and $\mu(\cdot \mid \text{compliers})$ is $\mu$ conditioned on the [compliers](compliers.md) (the zero measure when the compliers have measure $0$). When the compliers have measure $0$ both sides are $0$, so this identity is not by itself an identification of a complier average.
