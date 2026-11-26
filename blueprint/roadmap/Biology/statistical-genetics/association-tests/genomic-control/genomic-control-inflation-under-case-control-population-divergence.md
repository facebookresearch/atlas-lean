# Genomic-control inflation under case–control population divergence

**Setting.** A case–control study samples $N/2$ diploid cases from population $1$ and $N/2$ diploid controls from population $2$, so each group contributes $N$ chromosomes. (Any stratified design fits this frame by letting populations $1$ and $2$ be the appropriate mixtures of the underlying populations.) At a neutral biallelic marker let $p_1$, $p_2$ be the sample allele frequencies in cases and controls and $p = (p_1+p_2)/2$. Assume Hardy–Weinberg proportions within each population and that, under neutral drift since divergence together with binomial sampling,

$$p_1 - p_2 \sim \mathcal{N}\!\Bigl(0,\; p(1-p)\bigl(2F_{ST} + \tfrac{1}{N} + \tfrac{1}{N}\bigr)\Bigr),$$

where $F_{ST}$ is the drift variance of each population's frequency, in units of $p(1-p)$, about the ancestral frequency.

**Proposition.** The squared genotype–status correlation is, to leading order,

$$r^2 = \frac{(p_1-p_2)^2}{2p(1-p)},$$

so the Cochran–Armitage trend statistic $\chi^2_{CA} = N r^2$ satisfies

$$\chi^2_{CA} \sim (1 + N F_{ST})\,\chi^2_1 .$$

Hence the genomic-control inflation factor at null markers is

$$\lambda = 1 + N F_{ST},$$

and dividing every statistic by $\lambda$ restores a $\chi^2_1$ null distribution. More generally, because both the allele-frequency-difference statistic and $\chi^2_{CA}$ are proportional to $(p_1-p_2)^2/\bigl(p(1-p)\bigr)$, their distributions agree up to a constant factor even at markers that do not follow the neutral null.

**Consequence.** Stratification from recent drift inflates all markers by one common factor, which genomic control removes exactly; stratification from older divergence, which carries an excess of markers with unusually large frequency differences, is not of this form and is not removed by a single $\lambda$.

## Depends on

- [The Cochran–Armitage statistic is N r²](../cochran-armitage-trend-test/ca-stat-eq-mul-sample-corr-sq.md)
- [Common-inflation model of Gaussian null scores](common-inflation-model.md)
- [Wright's hierarchical F-statistics identity](../../../population-structure/wright-s-f-statistics/hierarchical-f-statistics.md)

## Proof depends on

- [The square of a standard normal variable is chi-square with one degree of freedom](../../../../Probability/distributions/continuous/chi-square-distribution/gaussian-real-map-sq.md): the squared Gaussian frequency difference

## Expansion

Code case status as $y \in \{0,1\}$ with half the sample cases and the genotype as $g \in \{0,1,2\}$. Then $\operatorname{Cov}(g,y) = \tfrac14\bigl(2p_1 - 2p_2\bigr) = (p_1-p_2)/2$, $\operatorname{Var}(y) = 1/4$ and, under Hardy–Weinberg proportions and ignoring the small between-group term, $\operatorname{Var}(g) \approx 2p(1-p)$, which gives the formula for $r^2$. Substituting the Gaussian law of $p_1 - p_2$ gives $\chi^2_{CA} = N(p_1-p_2)^2/(2p(1-p))$ distributed as $\tfrac{N}{2}\bigl(2F_{ST} + \tfrac{2}{N}\bigr)\chi^2_1 = (1+NF_{ST})\chi^2_1$. The factor is the same for every marker, so the null scores follow the common-inflation model with $\lambda = 1 + NF_{ST}$.

## Sources

- A. L. Price, A. Helgason, S. Palsson et al., "The impact of divergence time on the nature of population structure: an example from Iceland", PLoS Genetics (2009), Materials and Methods, "Relationship between the distributions of allele frequency differences and disease association statistics", <https://doi.org/10.1371/journal.pgen.1000505>, PMCID PMC2684636.
- B. Devlin and K. Roeder, "Genomic control for association studies", Biometrics (1999) (the genomic-control correction; background).
