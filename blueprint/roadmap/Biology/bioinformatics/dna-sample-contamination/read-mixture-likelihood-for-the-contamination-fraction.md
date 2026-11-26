# Read-mixture likelihood for the contamination fraction

**Model.** A DNA sample is assumed to be a mixture of the targeted individual (fraction $1-\alpha$) and one unrelated contaminating individual (fraction $\alpha \in [0,1]$), and the same fraction $\alpha$ of sequence reads is assumed to come from the contaminant. At biallelic sites $i = 1, \dots, M$ let $g_{i1}, g_{i2} \in \{0,1,2\}$ be the genotypes of the target and the contaminant, let $b_{ij}$ ($1 \le j \le R_i$) be the base calls of the reads covering site $i$, and let $e_{ij} \in \{0,1\}$ indicate a sequencing error, with $P(e_{ij}=1) = 10^{-Q_{ij}/10}$ for the phred base quality $Q_{ij}$; an error is equally likely to produce each of the three other bases. Each base call is drawn from the two-sample mixture

$$P(b_{ij} \mid g_{i1}, g_{i2}, e_{ij}; \alpha) = (1-\alpha)\,P(b_{ij} \mid g_{i1}, e_{ij}) + \alpha\,P(b_{ij} \mid g_{i2}, e_{ij}),$$

where $P(b \mid g, e)$ picks one of the two alleles of $g$ uniformly and then applies the error.

**Sequence-only likelihood.** With genotypes unknown and drawn independently from Hardy–Weinberg proportions $P(g)$ at known population allele frequencies, and sites and reads treated as independent,

$$L(\alpha) = \prod_{i=1}^{M} \sum_{g_{i1}} \sum_{g_{i2}} \Big\{ \prod_{j=1}^{R_i} \sum_{e_{ij}} \big[(1-\alpha) P(b_{ij} \mid g_{i1}, e_{ij}) + \alpha P(b_{ij} \mid g_{i2}, e_{ij})\big] P(e_{ij}) \Big\} P(g_{i2})\, P(g_{i1}).$$

Swapping the roles of the two individuals shows $L(\alpha) = L(1-\alpha)$, so $\alpha$ is identifiable only up to this reflection and is estimated on $[0, 1/2]$ by maximizing $L$ (grid search followed by Brent's method).

**With array genotypes of the target.** If an array genotype $G_i$ of the target is available, the target genotype is replaced by $P(g_{i1} \mid \varepsilon_i; G_i)$ with a genotyping-error indicator $\varepsilon_i$ ($g_{i1} = G_i$ when $\varepsilon_i = 0$), which breaks the symmetry; replacing $P(g_{i2})$ by the array-genotype law of a specific study individual $k$ and maximizing over $(\alpha, k)$ identifies the most likely contaminating sample.

## Expansion

The likelihood is a finite mixture over the unobserved genotype pair at each site, so it can be evaluated site by site in $O(\sum_i R_i)$ time. Contamination shows up as a surplus of reads carrying a third allele copy: at a site where the target is homozygous, a fraction near $\alpha/2$ or $\alpha$ of reads carry the other allele, depending on the contaminant's genotype. The model ignores relatedness: a contaminant sharing a fraction $f$ of alleles with the target is reported in simulations as contamination of about $(1-f)\alpha$, and several contaminating individuals inflate $\hat\alpha$ because they increase the number of distinct alleles observed per site.

## Sources

- G. Jun, M. Flickinger, K. N. Hetrick et al., "Detecting and estimating contamination of human DNA samples in sequencing and array-based genotype data", American Journal of Human Genetics 91 (2012), 839–848, Material and Methods (Equations 1 and 2), <https://doi.org/10.1016/j.ajhg.2012.09.004>, PMCID PMC3487130.
