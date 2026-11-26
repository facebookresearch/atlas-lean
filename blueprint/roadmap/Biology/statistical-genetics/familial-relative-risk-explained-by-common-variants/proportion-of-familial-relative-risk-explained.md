# Proportion of familial relative risk explained by a set of variants

Let a disease follow a log-additive polygenic model in which variant $i$ has minor allele frequency $p_i$ and per-allele log odds ratio $\beta_i$, estimated by $\hat\beta_i$ with standard error $\tau_i$, the variants being approximately independent. Let $\lambda > 1$ be the overall familial relative risk to first-degree relatives. The proportion of the familial relative risk explained by a set $\mathcal{V}$ of variants is

$$\Pi(\mathcal{V}) = \frac{\sum_{i \in \mathcal{V}} p_i (1 - p_i)\big(\hat\beta_i^{2} - \tau_i^{2}\big)}{\log \lambda},$$

where the numerator estimates half the variance of the polygenic log-risk score contributed by $\mathcal{V}$: for variant $i$ the genotype $G_i \in \{0,1,2\}$ has $\operatorname{Var}(G_i) = 2p_i(1-p_i)$ under Hardy-Weinberg equilibrium, so its contribution to the variance of $\sum_i \beta_i G_i$ is $2 p_i (1-p_i)\beta_i^{2}$.

## Expansion

Under a log-additive model the familial relative risk to first-degree relatives satisfies $\log \lambda = \tfrac{1}{2}\operatorname{Var}\big(\sum_i \beta_i G_i\big)$ for independent variants, because relatives share half their genome in expectation; the ratio above is therefore the share of that total contributed by $\mathcal{V}$. Subtracting $\tau_i^{2}$ is a bias correction: $\mathbb{E}[\hat\beta_i^{2}] = \beta_i^{2} + \tau_i^{2}$ for an unbiased estimator, so the raw sum of squared estimates systematically overstates the explained variance, most severely for variants whose effects are small relative to their standard errors. The estimator still inherits winner's curse when $\mathcal{V}$ is selected by significance in the same data, and it assumes the variants are in linkage equilibrium with each other, so correlated variants in one locus must be reduced to independent signals before summing.

## Sources

- Michailidou K, Lindstrom S, Dennis J, et al. Association analysis identifies 65 new breast cancer risk loci. *Nature* 551:92-94 (2017), Methods, estimation of the proportion of familial risk explained. DOI <https://doi.org/10.1038/nature24284>. PMCID PMC5798588.
