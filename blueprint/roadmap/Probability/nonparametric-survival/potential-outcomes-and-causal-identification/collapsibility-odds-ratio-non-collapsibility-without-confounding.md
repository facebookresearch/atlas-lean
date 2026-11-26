# Collapsibility of effect measures without confounding

A measure of association of $X$ and $Y$ is strictly collapsible across $Z$ if it is constant across the strata of $Z$ and this constant equals its value in the marginal table; collapsibility depends on the chosen measure, and a constant conditional odds ratio can differ from the marginal odds ratio (Greenland, Robins and Pearl 1999, Section 4 and Table 1). For a generalized linear regression of $Y$ on $X$ and $Z$, marginal independence of the regressors $X$ and $Z$ (the two exposure groups have the same distribution of $Z$) ensures collapsibility of the coefficient of $X$ over $Z$ only when the link is the identity or the logarithm (Gail, Wieand and Piantadosi; Gail; as stated by Greenland, Robins and Pearl). For binary $Y$ this is elementary: if $X \perp Z$ and the conditional risk difference (or risk ratio) of $X$ is the same in every stratum of $Z$, then averaging the stratum risks over the common law of $Z$ in both exposure groups gives the same marginal risk difference (or risk ratio), while the odds ratio, whose link is the logit, is not collapsible in general. Balance of $Z$ alone does not establish the absence of confounding; but when the exposure $X$ is randomized, independently of $Z$ and of the potential outcomes, there is no confounding and the odds ratio can still be non-collapsible, so non-collapsibility of the odds ratio is distinct from confounding (Greenland, Robins and Pearl 1999, Section 4, which compares the reference risk with the counterfactual risk of the target).

## Expansion

1. The model: the joint law of $(X, Z, Y)$ with $X \perp Z$, and the conditional and marginal effect measures.
2. Collapsibility of the risk difference and the risk ratio, by averaging over the law of $Z$.
3. Non-collapsibility of the odds ratio: an explicit two-stratum example with $X \perp Z$.
4. Attenuation: a constant conditional odds ratio different from $1$ gives a marginal odds ratio closer to $1$ whenever $Z$ is associated with $Y$ within exposure levels, as a separate statement with its exact hypotheses.
5. The distinction between non-collapsibility and confounding under randomized exposure, with the counterfactual definitions and the Table 2 example of the source.

## Sources

- S. Greenland, J. M. Robins and J. Pearl, Confounding and collapsibility in causal inference, Statist. Sci. 14 (1999), 29–46, Section 4 and Table 1. <https://doi.org/10.1214/ss/1009211805>
