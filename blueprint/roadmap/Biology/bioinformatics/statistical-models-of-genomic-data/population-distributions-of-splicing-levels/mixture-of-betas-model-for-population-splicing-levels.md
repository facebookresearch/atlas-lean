# Mixture-of-betas model for population splicing levels

**Setting.** For a splicing event in one tissue, the inclusion level of an individual is $\Psi \in [0, 1]$, the fraction of transcripts including the exon. It is observed through RNA-seq exon-junction reads: conditional on $\Psi$, the number of reads supporting the event is

$$\text{event reads} \mid \Psi \sim \mathrm{Binomial}\big(\text{EJ reads}_{\text{event}} + \text{EJ reads}_{\text{cognate}},\ \Psi\big). \tag{2}$$

Rarely used exons have few junction reads per sample, so the per-individual estimate of $\Psi$ from this binomial alone is noisy.

**Statement** (Jacobs et al. 2025, Methods, eqs. (2)–(5)). Pool information across individuals by giving $\Psi$ a population prior. A single beta prior $\Psi \sim \mathrm{Beta}(\alpha, \beta)$ (eq. (3)), with $\alpha$ and $\beta$ acting as pseudocounts for the event and its cognate junction, is conjugate to (2) but cannot represent a multimodal population. The model used instead is a three-component mixture, with nine parameters,

$$\Psi \sim \sum_{i=1}^{3} \gamma_i\, \mathrm{Beta}(\alpha_i, \beta_i), \qquad \gamma_i \ge 0,\ \sum_{i=1}^{3} \gamma_i = 1, \tag{4}$$

whose density is $\mathrm{PDF} = \sum_{i=1}^{3} \gamma_i\, \mathrm{PDF}_{\mathrm{Beta}(\alpha_i, \beta_i)}$ (eq. (5)), fitted by maximum likelihood per event and tissue; setting one or two weights to zero recovers the two- and one-component models. From the fitted population distribution, the summary statistic *exon frequency* at threshold $\psi_0$ is the estimated proportion of individuals whose $\Psi$ is at least $\psi_0$ (a $5\%$ threshold is used by default).

## Remarks

The hierarchical form is partial pooling: each individual's posterior $\Psi$ is shrunk towards the fitted population distribution by an amount set by that individual's read depth, so a handful of junction reads no longer produces an inclusion estimate near $0$ or $1$. Three components are chosen for a genetic reason: an event driven by one splicing quantitative trait locus has three genotype classes, each with its own typical inclusion level, giving a trimodal population distribution that no single beta can represent. The exon frequency is a functional of the fitted distribution rather than a count of individuals above the threshold, which is what makes it stable when per-individual estimates are uncertain; it plays the role for splicing events that allele frequency plays for variants, stratifying events into common and rare without requiring any individual's $\Psi$ to be precisely known.

## Sources

- H. N. Jacobs, B. L. Gorissen, J. Guez, M. Kanai, K. Gupta, H. K. Finucane, K. J. Karczewski and C. B. Burge, "Widespread naturally variable human exons aid genetic interpretation", Nature Communications 16 (2025), Methods ("Mixture of Betas binomial model") and Results (Figure 1A), eqs. (2)–(5), <https://doi.org/10.1038/s41467-025-65476-7>, PMCID PMC12727881.
