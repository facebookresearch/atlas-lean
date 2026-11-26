# Gamma-plus-lethal DFE and the among-species ratio of N_e

Let $S = 4N_e s$ be the population-scaled selection coefficient of a new nonsynonymous mutation, with $s < 0$ for deleterious mutations.

**Gamma-plus-lethal model.** A fraction $p_{\mathrm{lth}} \in [0,1)$ of nonsynonymous mutations is lethal, so they never segregate and contribute nothing to the observed site-frequency spectrum. The remaining fraction $1 - p_{\mathrm{lth}}$ has deleterious effects $-S$ distributed as a [gamma distribution](gamma-dfe.md) with mean $\bar S$ and shape $\beta$. The expected nonsynonymous spectrum is therefore $(1 - p_{\mathrm{lth}})$ times the [spectrum under the gamma DFE](dfe-sfs-gamma-dfe.md), fitted jointly with the synonymous spectrum, which carries the demographic and sampling nuisance parameters. The pure gamma model is the case $p_{\mathrm{lth}} = 0$.

**Ratio of drift power.** If two species share the distribution of unscaled effects $s$, in particular its mean $\bar s$, then

$$\frac{N_e^{(1)}}{N_e^{(2)}} = \frac{\bar S^{(1)}}{\bar S^{(2)}},$$

so the among-species ratio of effective size, the inverse ratio of the power of genetic drift, can be read off the fitted mean scaled selection coefficients. A shared shape $\beta$ across species is a necessary consistency check of the shared-DFE assumption.

**Empirical result.** Fitted to synonymous and nonsynonymous spectra of primates and fruit flies, the pure gamma model gives strongly different shape estimates among taxa, contradicting a shared DFE, while adding the lethal class largely reconciles them: the log-likelihood gain of species-specific over shared shapes drops from $281.9$ to $191.0$, although a shared shape is still formally rejected. Under it, $N_e$ varies among animal species by a factor of at least $500$, an order of magnitude more than synonymous diversity $\pi_S$ varies. This narrows Lewontin's paradox, the limited range of genetic diversity across species.

## Depends on

- [Gamma distribution of fitness effects](gamma-dfe.md)
- [Site-frequency spectrum under the gamma DFE](dfe-sfs-gamma-dfe.md)

## Expansion

Very strongly deleterious mutations have essentially zero probability of being seen as polymorphisms at realistic sample sizes, whatever $N_e$ is. A class of mutations whose fate does not scale with $N_e$ cannot be represented by a gamma law of $S = 4N_e s$ with an $N_e$-independent shape, so forcing it into a pure gamma fit distorts the shape estimate differently in small- and large-$N_e$ species. Modelling that class separately as lethal removes most of the distortion. Under the neutral equilibrium $\pi_S = 4N_e\mu$, so $\pi_S$ would track $N_e$; the gap between the $\bar S$ ratio and the $\pi_S$ ratio points to linked selection and demographic fluctuations depressing neutral diversity in large populations.

## Sources

- N. Galtier and M. Rousselle, "How Much Does Ne Vary Among Species?", *Genetics* (2020), <https://doi.org/10.1534/genetics.120.303622> (PMC7536855; section "Inference methods", Results and Discussion).
