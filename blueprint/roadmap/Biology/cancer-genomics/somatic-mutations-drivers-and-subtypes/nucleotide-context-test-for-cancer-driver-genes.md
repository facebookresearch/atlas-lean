# Nucleotide-context test for cancer driver genes

Fix a gene $g$ observed in a cohort of tumors, with $s_g$ synonymous and $n_g$ nonsynonymous somatic mutations at positions $\vec p_g = (p_1, \dots, p_{n_g})$. Assign every position $j$ of the gene a **context-dependent mutability** $\lambda_j > 0$ from a background model of passenger mutagenesis fitted to the cohort. Under the null hypothesis that all mutations in $g$ are passengers, the probability of the observed data factorizes into a regional term and a positional term,

$$P\bigl(n_g, \vec p_g \mid s_g; \vec\lambda_g\bigr) = \underbrace{P(n_g \mid s_g)}_{\text{regional mutation rate}} \cdot \underbrace{P\bigl(\vec p_g \mid n_g; \vec\lambda_g\bigr)}_{\text{nucleotide context}},$$

where $P(n_g \mid s_g)$ calibrates the gene's megabase-scale background rate by its synonymous count, and $P(\vec p_g \mid n_g; \vec\lambda_g)$ is the probability that $n_g$ passenger mutations fall at the observed positions, with positions weighted by their mutabilities, so that a configuration concentrated on low-mutability positions is improbable.

**Test.** Simulate random scenarios in which at least $n_g$ nonsynonymous mutations are placed along $g$ under the null model. The $p$-value of $g$ is the fraction of scenarios that have at least $n_g$ nonsynonymous mutations **and** a joint null probability lower than that of the observed data. A gene is thus significant either because it carries too many mutations for its regional rate, or because its mutations sit at positions of low mutability ("unusual" nucleotide contexts) that passengers rarely hit.

**Mutability model.** The mutability $\lambda_j$ is a composite-likelihood score in which the base substitution at $j$ and each flanking nucleotide in an extended window (beyond the trinucleotide context) contribute a separate multiplicative factor, instead of a free parameter for every possible context; samples are first grouped by Bayesian hierarchical clustering of their mutational processes.

## Expansion

Passenger mutations concentrate in contexts preferred by the active mutational processes (for example APOBEC or polymerase-$\varepsilon$ motifs), whereas driver mutations are placed by protein function, which is not tied to such contexts; mutations at low-mutability positions are therefore enriched for drivers. The factorized model separates these two sources of evidence and uses the second without knowing which positions are functional. The multiplicative composite likelihood avoids estimating $4^{w}$ context-specific rates for a window of width $w$, which would overfit sparse counts and absorb mutational hotspots; applied to trinucleotides it reproduces the COSMIC signature spectra, and heptanucleotide windows raised the observed–predicted correlation for C>T mutations in melanoma from 0.76 to 0.91. The same positional term is computed for synonymous mutations to filter genes with local deviations from the passenger context distribution, and the context $p$-value is combined with tests for positional clustering and for loss-of-function excess. Across 11,873 tumor–normal exome pairs the method identified 460 driver genes.

## Sources

- F. Dietlein, D. Weghorn, A. Taylor-Weiner, A. Richters, B. Reardon, D. Liu, E. S. Lander, E. M. Van Allen and S. R. Sunyaev, "Identification of cancer driver genes based on nucleotide context", Nature Genetics (2020), Results "A framework for identifying driver genes in cancer" (Eq. (1)) and "Context-dependent mutability of genomic positions" (details in the Supplementary Note), <https://doi.org/10.1038/s41588-019-0572-y>, PMCID PMC7031046.
