# Mendelian expectation of an offspring polygenic score

Fix $M$ biallelic autosomal loci and real weights $\beta_1, \dots, \beta_M$. For a diploid individual with allele counts $g_j \in \{0, 1, 2\}$ define the polygenic score

$$S = \sum_{j=1}^{M} \beta_j g_j .$$

Let a mother with counts $g^{\mathrm m}_j$ and a father with counts $g^{\mathrm f}_j$ have a child with counts $g^{\mathrm c}_j = T^{\mathrm m}_j + T^{\mathrm f}_j$, where $T^{\mathrm m}_j \in \{0,1\}$ is the allele transmitted by the mother at locus $j$ and similarly for the father. Assume **Mendelian segregation**: conditionally on the parental genotypes, each parent transmits each of its two alleles at locus $j$ with probability $1/2$, so $\mathbb{E}[T^{\mathrm m}_j \mid g^{\mathrm m}, g^{\mathrm f}] = g^{\mathrm m}_j / 2$ and likewise for the father. No independence between loci is assumed for the first statement.

**Proposition.** Writing $S_{\mathrm{MP}} = (S^{\mathrm m} + S^{\mathrm f})/2$ for the mid-parent score,

$$\mathbb{E}\big[S^{\mathrm c} \mid g^{\mathrm m}, g^{\mathrm f}\big] = S_{\mathrm{MP}} ,$$

hence $\mathbb{E}[S^{\mathrm c} - S_{\mathrm{MP}}] = 0$ for any distribution of parental genotypes (including stratified, admixed or assortatively mating populations), provided the offspring are not selected on a trait correlated with the transmissions.

If in addition the transmissions at different loci and from the two parents are independent given the parental genotypes (unlinked loci), then

$$\operatorname{Var}\big(S^{\mathrm c} - S_{\mathrm{MP}} \mid g^{\mathrm m}, g^{\mathrm f}\big) = \frac14 \sum_{j=1}^{M} \beta_j^2 \big(H^{\mathrm m}_j + H^{\mathrm f}_j\big),$$

where $H^{\mathrm m}_j = \mathbf 1[g^{\mathrm m}_j = 1]$ and $H^{\mathrm f}_j = \mathbf 1[g^{\mathrm f}_j = 1]$ indicate heterozygous parents.

## Depends on

- [Mendel's law of segregation](../../../../population-genetics/hardy-weinberg-law/transmit.md)

## Expansion

By linearity, $\mathbb{E}[S^{\mathrm c} \mid g^{\mathrm m}, g^{\mathrm f}] = \sum_j \beta_j (g^{\mathrm m}_j/2 + g^{\mathrm f}_j/2) = S_{\mathrm{MP}}$; only marginal Mendelian transmission probabilities enter, so linkage between loci does not matter. A homozygous parent transmits a deterministic allele, contributing no segregation variance; a heterozygous parent transmits a Bernoulli$(1/2)$ allele with variance $1/4$. Under independence of transmissions the variances add, giving the formula. The proposition is the polygenic analogue of the single-locus fact that a heterozygous parent transmits each allele with probability $1/2$, which underlies the classical TDT. Selecting children on a phenotype associated with $S$ (for example, affected probands of unaffected parents) breaks the identity, and the size of $\mathbb{E}[S^{\mathrm c} - S_{\mathrm{MP}} \mid \text{affected}]$ measures over-transmission.

## Sources

- D. J. Weiner, E. M. Wigdor, S. Ripke et al., "Polygenic transmission disequilibrium confirms that common and rare variation act additively to create risk for autism spectrum disorders", Nature Genetics 49 (2017), Results (expected offspring score equals the mid-parent score) and Online Methods "pTDT", <https://doi.org/10.1038/ng.3863>, PMCID PMC5552240.
