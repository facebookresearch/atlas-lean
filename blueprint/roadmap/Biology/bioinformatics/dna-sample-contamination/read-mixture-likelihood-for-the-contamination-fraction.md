# Read-mixture likelihood for the contamination fraction

**Model.** A DNA sample is assumed to be a mixture of the targeted individual (fraction $1-\alpha$) and one unrelated contaminating individual (fraction $\alpha \in [0,1]$), and the same fraction $\alpha$ of sequence reads is assumed to come from the contaminant. At biallelic sites $i = 1, \dots, M$ let $g_{i1}, g_{i2} \in \{0,1,2\}$ be the genotypes of the target and the contaminant, let $b_{ij}$ ($1 \le j \le R_i$) be the base calls of the reads covering site $i$, and let $e_{ij} \in \{0,1\}$ indicate a sequencing error, with $P(e_{ij}=1) = 10^{-Q_{ij}/10}$ for the phred base quality $Q_{ij}$; an error is equally likely to produce each of the three other bases. Each base call is drawn from the two-sample mixture

$$P(b_{ij} \mid g_{i1}, g_{i2}, e_{ij}; \alpha) = (1-\alpha)\,P(b_{ij} \mid g_{i1}, e_{ij}) + \alpha\,P(b_{ij} \mid g_{i2}, e_{ij}),$$

where $P(b \mid g, e)$ picks one of the two alleles of $g$ uniformly and then applies the error.

**Sequence-only likelihood.** Assume that the genotypes $g_{i1}, g_{i2}$ are unknown and independent, each drawn from the [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md) $P(g)$ at known population allele frequencies, independently across sites, and that, **conditionally on the genotype pair $(g_{i1}, g_{i2})$ of their site**, the reads at that site are independent, each read's error indicator $e_{ij}$ is independent of everything else and its base call follows the mixture above. Reads at one site are not marginally independent: they share the unknown genotype pair, which is why the product over reads lies inside the sums over genotypes. The likelihood is

$$L(\alpha) = \prod_{i=1}^{M} \sum_{g_{i1}} \sum_{g_{i2}} \Big\{ \prod_{j=1}^{R_i} \sum_{e_{ij}} \big[(1-\alpha) P(b_{ij} \mid g_{i1}, e_{ij}) + \alpha P(b_{ij} \mid g_{i2}, e_{ij})\big] P(e_{ij}) \Big\} P(g_{i2})\, P(g_{i1}).$$

Since the two genotypes have the same prior, swapping the roles of the two individuals shows $L(\alpha) = L(1-\alpha)$. This reflection is a necessary ambiguity of these data, not a guarantee that $\alpha$ is identified on $[0, 1/2]$: with one read per site every $\alpha$ has the same likelihood, since, writing $P(b \mid g) = \sum_{e} P(b \mid g, e) P(e)$, each site contributes $\sum_{g_1, g_2} P(g_1) P(g_2) \big[(1-\alpha) P(b \mid g_1) + \alpha P(b \mid g_2)\big] = \sum_g P(g) P(b \mid g)$. The source restricts the estimate to $[0, 1/2]$ and maximizes $L$ there (grid search followed by Brent's method).

**With array genotypes of the target.** If an array genotype $G_i$ of the target is available, the prior $P(g_{i1})$ is replaced by its marginal over a binary genotyping-error indicator $\varepsilon_i$ with probabilities $P(\varepsilon_i)$:

$$P(g_{i1} \mid G_i) = \sum_{\varepsilon_i \in \{0, 1\}} P(g_{i1} \mid \varepsilon_i; G_i)\, P(\varepsilon_i),$$

where $P(g_{i1} = G_i \mid \varepsilon_i = 0; G_i) = 1$ and, on a genotyping error, $g_{i1}$ is each of the two genotypes other than $G_i$ with probability $1/2$. The likelihood keeps the sum over $\varepsilon_i$ inside the product over sites, alongside the sums over $g_{i1}$ and $g_{i2}$. This prior differs for the two individuals and breaks the reflection symmetry; replacing $P(g_{i2})$ by the same array-genotype law for a specific study individual $k$ and maximizing over $(\alpha, k)$ identifies the most likely contaminating sample.

## Expansion

The likelihood is a finite mixture over the unobserved genotype pair at each site, so it can be evaluated site by site in $O(\sum_i R_i)$ time. Contamination shows up as a surplus of reads carrying a third allele copy: at a site where the target is homozygous, a fraction near $\alpha/2$ or $\alpha$ of reads carry the other allele, depending on the contaminant's genotype. The model ignores relatedness: a contaminant sharing a fraction $f$ of alleles with the target is reported in simulations as contamination of about $(1-f)\alpha$, and several contaminating individuals inflate $\hat\alpha$ because they increase the number of distinct alleles observed per site.

## Depends on

- [Offspring genotype law under random union of gametes](../../population-genetics/hardy-weinberg-law/offspring.md)
- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- G. Jun, M. Flickinger, K. N. Hetrick et al., "Detecting and estimating contamination of human DNA samples in sequencing and array-based genotype data", American Journal of Human Genetics 91 (2012), 839–848, Material and Methods (Equations 1 and 2), <https://doi.org/10.1016/j.ajhg.2012.09.004>, PMCID PMC3487130.
