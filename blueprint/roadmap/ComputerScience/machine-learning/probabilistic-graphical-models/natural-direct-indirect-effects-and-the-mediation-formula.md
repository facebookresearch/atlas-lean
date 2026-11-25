# Natural direct/indirect effects and the mediation formula

Consider a finite recursive structural causal model with binary treatment $X$, finite-valued mediator
$Z$ and outcome $Y$, and nested counterfactuals $Y_{x, Z_{x'}}$. The natural direct effect of changing
$x_0$ to $x_1$ is $\mathrm{NDE} = \mathbb{E}[Y_{x_1, Z_{x_0}}] - \mathbb{E}[Y_{x_0}]$ and the natural indirect
effect is $\mathrm{NIE} = \mathbb{E}[Y_{x_0, Z_{x_1}}] - \mathbb{E}[Y_{x_0}]$. Assume that there is no
unmeasured confounding of the $X$–$Y$, $X$–$Z$ and $Z$–$Y$ relations, that no confounder of $Z$ and $Y$ is
affected by $X$, and positivity: $P(X = x) > 0$ for $x \in \{x_0, x_1\}$, and $P(Z = z, X = x) > 0$ for both values of
$x$ whenever $P(Z = z \mid X = x_0) > 0$ or $P(Z = z \mid X = x_1) > 0$. Then

$$\mathrm{NDE} = \sum_z \bigl(\mathbb{E}[Y \mid X = x_1, Z = z] - \mathbb{E}[Y \mid X = x_0, Z = z]\bigr) P(Z = z \mid X = x_0),$$

$$\mathrm{NIE} = \sum_z \mathbb{E}[Y \mid X = x_0, Z = z] \bigl(P(Z = z \mid X = x_1) - P(Z = z \mid X = x_0)\bigr).$$

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Finite recursive structural causal models.

## Related topics

- [The back-door adjustment](causal-bayesian-networks/backdoor-adjustment.md)

## Sources

- J. Pearl, *Direct and indirect effects*, UAI 2001, 411–420 (technical report R-273): definitions of the average natural direct and indirect effects, Theorem 2 (nonexperimental identification of the natural direct effect from a covariate set $W$ of covariates that are not descendants of $X$ or $Z$; the formulas above are the case $W = \emptyset$) and Theorem 4 with Eqs. (22)–(23) for the indirect effect. <https://ftp.cs.ucla.edu/pub/stat_ser/R273-U.pdf>
