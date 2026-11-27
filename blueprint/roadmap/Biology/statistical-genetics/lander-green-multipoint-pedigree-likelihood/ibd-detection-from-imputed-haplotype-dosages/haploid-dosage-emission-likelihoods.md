# Haploid-dosage emission likelihoods for IBD states

At a biallelic marker with alternative-allele frequency $p \in (0,1)$, let the observed data be the four **haploid dosages** $D = (x_{1A}, x_{1B}, x_{2A}, x_{2B})$, $x_h = P(g_h = 1) \in [0,1]$, the probabilities that each phased haplotype carries the alternative allele. Assume Hardy–Weinberg proportions for the prior $P(\mathbf g)$ of the latent alleles $\mathbf g = (g_{1A}, g_{1B}, g_{2A}, g_{2B}) \in \{0,1\}^4$, and $P(\mathbf g \mid D) = \prod_h [g_h x_h + (1-g_h)(1-x_h)]$. Up to a factor that is the same for all states,

$$P(D \mid s) \propto \sum_{\mathbf g \in \{0,1\}^4} \frac{P(\mathbf g \mid D)}{P(\mathbf g)}\, P(\mathbf g \mid s). \qquad (5)$$

For the non-IBD state $P(\mathbf g \mid s = 0) = P(\mathbf g)$, and for the IBD state $s = 1$ (haplotypes $1A$ and $2A$ share one allele drawn once from the population) this gives

$$P(D \mid s = 0) = 1, \qquad P(D \mid s = 1) = \frac{x_{1A} x_{2A}}{p} + \frac{(1-x_{1A})(1-x_{2A})}{1-p}, \qquad (7),(8)$$

and the other IBD states follow by permuting haplotypes.

The dosages are obtained from imputation output (the most likely phased genotype and three unphased genotype posteriors $p_0, p_1, p_2$): $P_{00} = p_0$, $P_{11} = p_2$; if $p_1$ is the largest, the heterozygote probability $p_1$ is assigned to the called phase ($P_{01} = p_1, P_{10} = 0$ for $0|1$, the reverse for $1|0$), otherwise $P_{01} = P_{10} = p_1/2$; then $x_{1A} = P_{11} + P_{10}$ and $x_{1B} = P_{11} + P_{01}$.

## Depends on

- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Expansion

By Bayes' rule $P(D \mid \mathbf g) = P(\mathbf g \mid D) P(D)/P(\mathbf g)$, and $P(D)$ is common to all states, which gives Eq. (5) (posterior state probabilities of the HMM are invariant to constant factors). For $s = 0$ the prior cancels and $\sum_{\mathbf g} P(\mathbf g \mid D) = 1$. For $s = 1$ the factors of the non-shared haplotypes $1B, 2B$ cancel in the same way. For the shared pair, $P(\mathbf g \mid s = 1)$ is nonzero only when $g_{1A} = g_{2A} = a$, with probability $p_a$ ($p_1 = p$, $p_0 = 1-p$), while $P(\mathbf g)$ contributes $p_a^2$ and $P(\mathbf g \mid D)$ contributes $x_{1A}x_{2A}$ or $(1-x_{1A})(1-x_{2A})$; summing over $a$ gives Eq. (8). The likelihood ratio rewards concordant confident dosages at rare alleles: if both haplotypes surely carry an allele of frequency $p$, the IBD state is favoured by the factor $1/p$.

## Sources

- H. Ringbauer, Y. Huang, A. Akbari, S. Mallick, I. Olalde, N. Patterson and D. Reich, "Accurate detection of identity-by-descent segments in human ancient DNA", Nature Genetics 56 (2024), Methods ("Emission probabilities", Equations 2–8), <https://doi.org/10.1038/s41588-023-01582-w>, PMCID: PMC10786714.
