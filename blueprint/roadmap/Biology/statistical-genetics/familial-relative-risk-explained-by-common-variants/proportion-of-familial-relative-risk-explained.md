# Proportion of familial relative risk explained by a set of variants

Let a disease follow a log-additive polygenic model in which variant $i$ has minor allele frequency
$p_i \in (0,1)$ and per-allele log odds ratio $\beta_i$, estimated by $\hat\beta_i$ with standard error
$\tau_i$, the variants being approximately independent and each genotype $G_i \in \{0,1,2\}$ following
the [Hardy–Weinberg genotype law](../../population-genetics/hardy-weinberg-law/offspring.md), so that
$\operatorname{Var}(G_i) = 2p_i(1-p_i)$. Let $\lambda > 1$ be the overall familial relative risk to
first-degree relatives, a [recurrence-risk ratio](../risch-recurrence-risk-ratios-for-multilocus-trai/recurrence-ratio.md)
taken as an external input (the source uses $\lambda = 2$). The source's estimator of the proportion of
the familial relative risk explained by a set $\mathcal{V}$ of variants is

$$\hat\Pi(\mathcal{V}) = \frac{\sum_{i \in \mathcal{V}} p_i (1 - p_i)\big(\hat\beta_i^{2} - \tau_i^{2}\big)}{\log \lambda}.$$

Its numerator estimates $\sum_{i \in \mathcal{V}} p_i(1-p_i)\beta_i^{2}$, half the contribution of
$\mathcal{V}$ to the variance $\sum_i 2p_i(1-p_i)\beta_i^{2}$ of the log-risk score $\sum_i \beta_i G_i$,
and the ratio is read as the share of $\log \lambda$ attributable to $\mathcal{V}$. This is an
estimator under a model-based approximation, not an exact decomposition of $\log \lambda$. Because of
the bias correction, $\hat\Pi(\mathcal{V})$ is negative whenever
$\sum_{i \in \mathcal{V}} p_i(1-p_i)\hat\beta_i^{2} < \sum_{i \in \mathcal{V}} p_i(1-p_i)\tau_i^{2}$, and
nothing confines it to $[0,1]$.

## Depends on

- [Risch's recurrence-risk ratio](../risch-recurrence-risk-ratios-for-multilocus-trai/recurrence-ratio.md)
- [Offspring genotype law under random union of gametes](../../population-genetics/hardy-weinberg-law/offspring.md)

## Expansion

The approximation behind the denominator: if risk is multiplicative across independent loci with
per-allele log risk $\beta_i$ (the odds ratio approximating the risk ratio for a rare disease) and the
outcomes of two relatives are conditionally independent given their genotypes, the log recurrence-risk
ratio contributed by locus $i$ is
$\log \mathbb{E}\,e^{\beta_i(G_i + G'_i)} - 2\log \mathbb{E}\,e^{\beta_i G_i}$, whose expansion to second
order in $\beta_i$ is $\beta_i^{2}\operatorname{Cov}(G_i, G'_i) = p_i(1-p_i)\beta_i^{2}$ for a
parent–offspring pair, which shares one allele identical by descent. Summing over loci gives
$\log \lambda \approx \tfrac{1}{2}\operatorname{Var}\big(\sum_i \beta_i G_i\big)$ only to second order and
only for the part of $\lambda$ the modelled variants carry. The relation is not exact: at one
Hardy–Weinberg locus with allele frequency $1/2$ and disease probabilities $1/2$, $2/3$ and $4/5$ for
$0$, $1$ and $2$ alleles (odds doubling per allele), a parent–offspring pair with conditionally
independent outcomes has relative risk $6322/6241 \approx 1.013$, while
$\exp\big((\log 2)^{2}/4\big) \approx 1.128$. Subtracting $\tau_i^{2}$ is a bias correction:
$\mathbb{E}[\hat\beta_i^{2}] = \beta_i^{2} + \tau_i^{2}$ for an unbiased estimator, so the raw sum of squared estimates systematically
overstates the explained variance, most severely for variants whose effects are small relative to
their standard errors. The estimator still inherits winner's curse when $\mathcal{V}$ is selected by
significance in the same data, and it assumes the variants are in linkage equilibrium with each other,
so correlated variants in one locus must be reduced to independent signals before summing.

## Sources

- Michailidou K, Lindstrom S, Dennis J, et al. Association analysis identifies 65 new breast cancer risk loci. *Nature* 551:92-94 (2017), Methods, estimation of the proportion of familial risk explained. DOI <https://doi.org/10.1038/nature24284>. PMCID PMC5798588.
