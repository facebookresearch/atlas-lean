# LD contrast test and composite linkage disequilibrium

**Composite LD.** For biallelic loci $A,B$ with allele frequencies $p=p(A)$, $q=p(B)$, gametic LD is $D=p(AB)-p(A)p(B)$. When phase is unknown, the composite LD

$$\mathrm{CLD}=p_{AB}+p_{A/B}-2p(A)p(B)$$

sums the frequency of $A$ and $B$ on the same gamete ($p_{AB}$) and on the two different gametes of an individual ($p_{A/B}$). With additive $0/1/2$ genotype codes, the sample correlation of genotypes satisfies

$$\hat r_{\text{genotype}}=\frac{\mathrm{CLD}}{\sqrt{(p(1-p)+D_A)(q(1-q)+D_B)}}\approx\frac{\mathrm{CLD}}{\sqrt{p(1-p)q(1-q)}},$$

where $D_A=p_{AA}-p^2$ and $D_B=p_{BB}-q^2$ are Hardy–Weinberg disequilibria (near $0$ after quality control). In particular, $\mathrm{CLD}$ is (up to scaling) the sample covariance of the two genotype codes, the analogue of $\hat r_{\text{allele}}=D/\sqrt{p(1-p)q(1-q)}$ for haplotypes.

**LD contrast test.** For a pair of SNPs, with $\widehat{\mathrm{CLD}}$ estimated separately in independent case and control samples,

$$\chi^2=\frac{\big(\widehat{\mathrm{CLD}}_{\text{case}}-\widehat{\mathrm{CLD}}_{\text{control}}\big)^2}{\operatorname{Var}\widehat{\mathrm{CLD}}_{\text{case}}+\operatorname{Var}\widehat{\mathrm{CLD}}_{\text{control}}}$$

is asymptotically $\chi^2_1$ under the null hypothesis of equal LD in cases and controls.

## Depends on

- [Gametic linkage disequilibrium](../../../quantitative-genetics/dominance-linkage-disequilibrium/ld-d.md)
- [Deviation from Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/hw-deviation.md)
- [Chi-square distribution](../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Expansion

If the population is in linkage equilibrium and disease risk is a non-multiplicative (interacting) function of two loci, conditioning on disease status induces association between the loci among cases, while controls (for a rare disease) stay close to the population; a difference of LD is therefore evidence of interaction even between unlinked loci. Using genotypes instead of phased haplotypes amounts to splitting double heterozygotes equally between the two phases, which is why CLD is a genotype covariance. Under the null, each sample CLD is asymptotically normal, so the standardized difference is asymptotically standard normal and its square is $\chi^2_1$.

## Sources

- Zhang S, Jiang W, Ma RC, Yu W, "Region-based interaction detection in genome-wide case-control studies" (2019), equations (1)-(5) (composite LD, its relation to genotype correlation and the LD contrast statistic), <https://doi.org/10.1186/s12920-019-0583-7>, PMCID PMC6936067.
