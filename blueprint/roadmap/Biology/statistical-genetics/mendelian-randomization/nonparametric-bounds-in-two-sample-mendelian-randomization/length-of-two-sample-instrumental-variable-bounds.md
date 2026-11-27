# Length of two-sample instrumental variable bounds

Let $X$ and $Y$ be a binary exposure and outcome, $Z \in \{0,1,2\}$ a genetic instrument (a SNP genotype) and $U$ an unmeasured confounder, with potential outcomes $Y^{z,x}$. Assume SUTVA and the instrumental-variable conditions: relevance ($Z \not\perp X$), independence ($Z \perp U$), exclusion ($Y^{z,x} = Y^{x}$ for all $z$), and conditional ignorability ($Y^{z,x} \perp (Z, X) \mid U$). In a two-sample design only the marginal conditionals $P(X = 1 \mid Z = z)$ and $P(Y = 1 \mid Z = z)$ are observed, from separate samples. Define the instrument strength

$$\mathrm{ST} = \max_{z \ne z'}\left|P(X = 1 \mid Z = z) - P(X = 1 \mid Z = z')\right|.$$

The average treatment effect $\mathrm{ATE} = E[Y^1 - Y^0]$ is then confined to an explicit interval whose endpoints are maxima and minima of finitely many linear combinations of these conditionals, and these sharp two-sample bounds come with checkable linear inequality constraints on the observed data.

**Theorem.** Under the assumptions above and a two-sample design, a sharp upper bound on the length of the two-sample bounds for the ATE is

$$2 - 2\,\mathrm{ST},$$

i.e. the length never exceeds $2 - 2\,\mathrm{ST}$, and some data-generating process satisfying the assumptions attains it. In a one-sample design the Balke–Pearl bounds for a binary or three-level instrument have length $1 - \mathrm{ST}$, so two-sample bounds can be twice as wide, and they are guaranteed to be shorter than $1$ only when $\mathrm{ST} > 1/2$.

## Depends on

- [Instrumental inequality and Balke-Pearl bounds](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/instrumental-inequality-and-balke-pearl-bounds.md)

## Expansion

Without the joint distribution of $(X, Y)$ given $Z$, many more joint laws are compatible with the observed margins, so the extremal ATE over all compatible structural models moves further apart; the worst case doubles the one-sample gap. Typical genome-wide significant variants change exposure prevalence by a few percentage points, so $\mathrm{ST}$ is small, the bounds usually have length above $1$, and they rarely exclude a null effect unless the instrument has an odds ratio of several units on the exposure.

## Sources

- R. M. Trane and H. Kang, "Nonparametric bounds in two-sample summary-data Mendelian randomization: some cautionary tales for practice", *Statistics in Medicine* (2022), Section 2.1, Eq. (1), Section 2.3, Eqs. (4)–(5), and Section 3.1, Theorem 1. <https://doi.org/10.1002/sim.9368> (PMC9314714)
