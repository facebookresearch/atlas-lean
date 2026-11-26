# Front-door adjustment formula

In the setting of the [back-door adjustment formula](back-door-adjustment.md), a set $Z$ satisfies the **front-door criterion** relative to an ordered pair $(X, Y)$ if

1. $Z$ intercepts every directed path from $X$ to $Y$,
2. there is no unblocked back-door path from $X$ to $Z$, and
3. every back-door path from $Z$ to $Y$ is blocked by $X$.

**Theorem.** If $Z$ satisfies the front-door criterion relative to $(X, Y)$ and $P(x, z) > 0$ for all relevant $x, z$, then

$$P(y \mid \operatorname{do}(x)) = \sum_{z} P(z \mid x) \sum_{x'} P(y \mid x', z)\, P(x').$$

This identifies the effect of $X$ on $Y$ even when $X$ and $Y$ share an unobserved common cause, provided the effect is fully mediated by an observed $Z$ that the confounder does not affect.

## Expansion

By condition 2, $\emptyset$ satisfies the back-door criterion for $(X, Z)$, so $P(z \mid \operatorname{do}(x)) = P(z \mid x)$. By condition 3, $X$ satisfies the back-door criterion for $(Z, Y)$, so $P(y \mid \operatorname{do}(z)) = \sum_{x'} P(y \mid x', z) P(x')$. By condition 1 all of the effect of $X$ on $Y$ passes through $Z$, so $P(y \mid \operatorname{do}(x)) = \sum_z P(z \mid \operatorname{do}(x)) P(y \mid \operatorname{do}(z))$; combining the two steps gives the formula.

## Depends on

- [Back-door adjustment formula](back-door-adjustment.md)

## Sources

- J. Pearl, "Causal diagrams for empirical research", *Biometrika* 82 (1995), 669–688, <https://doi.org/10.1093/biomet/82.4.669>. The front-door criterion and its adjustment theorem; stated in the canonical form (full text not available; no theorem numbers cited).
