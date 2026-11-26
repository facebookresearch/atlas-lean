# Logit-linear mixed-model test for directional selection

**Data.** Individuals (or clusters of individuals with similar ancestry and date) $i = 1,\dots,n$ are sampled at dates $t_i \le 0$ in the past (time measured backwards from the present, in fixed generation units). At a biallelic variant $j$, cluster $i$ of $n_i$ diploid individuals carries an allele count drawn from $\mathrm{Bin}(2n_i, p_{ij})$, where $p_{ij}$ is the frequency of the allele in the population cluster $i$ comes from.

**Model.** The log-odds of the frequency follow a generalized linear mixed model

$$\ln\frac{p_{ij}}{1-p_{ij}} = \alpha_j + s_j\, t_i + g_{ij}, \qquad \mathbf{g}_j \sim \mathcal{N}\bigl(\mathbf{0},\, \sigma_j^2 K\bigr),$$

with intercept $\alpha_j$, a selection coefficient $s_j$ assumed constant over time and space, and a structured random effect $\mathbf{g}_j$ whose covariance is the cluster-level genetic relationship matrix

$$K_{mn} = \frac{1}{N_m N_n}\sum_{i \in c_m}\sum_{i' \in c_n} A_{ii'}, \qquad A_{ii'} = \frac{1}{M}\sum_{k=1}^{M}\frac{(G_{ik}-2f_k)(G_{i'k}-2f_k)}{2f_k(1-f_k)},$$

where $c_m$ is the set of $N_m$ individuals in cluster $m$, $G_{ik}$ the genotype of individual $i$ at SNP $k$, and $f_k$ the overall allele frequency (computed leaving out the chromosome of the tested variant). The drift variance $\sigma_j^2$ is refitted at every variant but bounded below by the genome-wide value for its minor allele frequency.

**Test.** Directional selection at $j$ is the hypothesis $s_j \ne 0$: the sampling date predicts frequency differences beyond what genome-wide relatedness (population structure and drift) predicts. The estimate $\hat s_j$ and its standard error give $Z_j = \hat s_j/\mathrm{SE}(\hat s_j)$. The share of logit-scale frequency variance attributed to the trend is

$$\frac{s_j^2\operatorname{Var}(t)}{s_j^2\operatorname{Var}(t) + \sigma_j^2}.$$

**Calibration.** Unmodelled features of real data inflate the naive $Z_j^2$ well above $\chi^2_1$ (median inflation $4.75$ in the source), so significance is assessed empirically, from the enrichment of genome-wide association signals among variants with large $|Z_j|$, rather than from the normal tail.

## Depends on

- [Log-odds grow linearly under repeated haploid selection on two types](../../population-genetics/haploid-selection-and-multiplicative-fitnesses/log-odds-iterate-select.md)
- [Genetic relationship matrix entry](../../quantitative-genetics/genomic-relationship-matrices/grm.md)
- [Binomial law as a probability measure](../../../Probability/central-limit-theorems/poisson-limit-theorem/binomial-prob-measure.md)

## Expansion

Constant genic selection makes the log-odds of the allele frequency change by a fixed amount per generation regardless of the current frequency, so a linear trend on the logit scale is the natural fixed effect. Migration and drift also move frequencies, but they move all variants in a way captured by the relatedness of the samples; the random effect with covariance proportional to $K$ absorbs that shared component. Refitting $\sigma_j^2$ and $\alpha_j$ per variant absorbs site-specific drift (for example extra drift from background selection) and frequency effects. Principal components are avoided as covariates because in a time transect they correlate with sample date, which is collinear with the effect being tested. The assumption of a single constant $s_j$ misses fluctuating selection whose direction reverses within the transect.

## Sources

- A. Akbari, A. Perry, A. R. Barton et al., "Ancient DNA reveals pervasive directional selection across West Eurasia", Nature (2026), Methods, "Testing for selection while correcting for population structure" (Eq. 1), "Proportion of variance explained by directional selection" (Eq. 2), "Covariance structure for the GLMM" (Eqs. 3–4), and "Test of selection on single variants", <https://doi.org/10.1038/s41586-026-10358-1>, PMCID PMC13189228.
