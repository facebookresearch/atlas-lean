# Partition Bayes factors for direct and indirect phenotype association

**Model.** Let $g$ be the genotype at a variant (treated as a randomized intervention) and $Y = (Y_1,\dots,Y_d)$ a vector of measured phenotypes. A **partition** $\gamma = (U, D, I)$ splits the phenotype indices into disjoint sets of **unassociated**, **directly associated** and **indirectly associated** traits, with the restriction that $I = \emptyset$ whenever $D = \emptyset$. The model attached to $\gamma$ satisfies

- (C1) $Y_U$ is independent of $g$;
- (C2) $Y_I$ is conditionally independent of $g$ given $(Y_U, Y_D)$,

so its likelihood factorizes as

$$p(Y \mid g, \gamma) = p(Y_U)\; p(Y_D \mid Y_U, g)\; p(Y_I \mid Y_U, Y_D).$$

The global null $H_0$ (no association) is $\gamma_0 = (\{1,\dots,d\}, \emptyset, \emptyset)$, with $p(Y \mid g, H_0) = p(Y_U)\,p(Y_D \mid Y_U)\,p(Y_I\mid Y_U, Y_D)$ for any split.

**Proposition (partitions are conditional tests).** With fully specified (prior-integrated) conditional distributions, the Bayes factor of $\gamma$ against $H_0$ is

$$\mathrm{BF}_\gamma = \frac{p(Y \mid g,\gamma)}{p(Y \mid g, H_0)} = \frac{p(Y_D \mid Y_U, g)}{p(Y_D \mid Y_U)},$$

the Bayes factor for association of $Y_D$ with $g$ controlling for $Y_U$ and ignoring $Y_I$. Univariate tests ($D$ one trait, others in $I$), conditional tests ($D$ one trait, others in $U$) and the full multivariate test ($D$ everything) are special cases.

**Model averaging.** With prior weights $w_\gamma \propto \pi(\gamma)$ over non-null partitions, normalized to sum to one, the overall evidence against the global null is

$$\mathrm{BF}_{\mathrm{av}} = \sum_{\gamma \ne \gamma_0} w_\gamma\, \mathrm{BF}_\gamma, \qquad \frac{\Pr(H_0^c \mid Y)}{\Pr(H_0 \mid Y)} = \frac{\pi_0^c}{\pi_0}\,\mathrm{BF}_{\mathrm{av}},$$

and the posterior on $\gamma$ gives marginal probabilities that each trait lies in $U$, $D$ or $I$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The factors $p(Y_U)$ and $p(Y_I \mid Y_U, Y_D)$ are common to the alternative and the null and cancel in the ratio, leaving the conditional likelihood ratio. A threshold test on $\mathrm{BF}_\gamma$ is most powerful for $\gamma$ against $H_0$ by Neyman–Pearson. Two consequences: if only one trait is associated, conditioning on the others (not the univariate test) is most powerful; if all traits are associated but only one directly, the univariate test of that trait is most powerful. Averaging makes the evidence coherent: the posterior probability that any single trait is associated never exceeds the posterior probability that some trait is, a property that does not hold for $p$-values from separate univariate and multivariate tests.

## Sources

- M. Stephens, "A unified framework for association analysis with multiple related phenotypes", PLoS ONE 8(7) (2013) e65245, conditions C1–C2 and Eqs (1), (5)–(9), <https://doi.org/10.1371/journal.pone.0065245>, PMCID PMC3702528.
