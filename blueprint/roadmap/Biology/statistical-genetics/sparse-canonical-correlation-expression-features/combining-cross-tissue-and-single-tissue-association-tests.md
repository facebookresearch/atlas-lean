# Combining cross-tissue and single-tissue association tests

**Setting.** For one gene, TWAS proceeds in three steps: test each expression feature for cis-heritability, build an elastic-net predictor $w$ of the heritable features from the cis-SNPs, and form

$$Z_{\mathrm{TWAS}} = \frac{w^{\mathsf T} Z}{\sqrt{w^{\mathsf T} \Sigma_{s,s} w}},$$

where $Z$ is the vector of GWAS Wald $z$-scores at the cis-SNPs and $\Sigma_{s,s}$ their LD matrix from a reference panel; under the null $Z_{\mathrm{TWAS}}$ is standard normal. Applying this to the [sparse canonical correlation features](sparse-canonical-correlation-features-for-cross-tissue-expression.md) gives up to three cross-tissue $z$-scores, and applying it tissue by tissue gives one $z$-score per tissue.

**Statement** (Feng et al. 2021, Methods). The per-gene $p$-values from the heritable features, cross-tissue and single-tissue together, are combined by the aggregated Cauchy association test: for $p$-values $p_1, \dots, p_m$ with nonnegative weights $u_1, \dots, u_m$ summing to one, the statistic

$$T = \sum_{j=1}^{m} u_j \tan\!\big((0.5 - p_j)\pi\big)$$

is referred to the standard Cauchy distribution, giving $p = \tfrac12 - \arctan(T)/\pi$. The alternatives compared are a Bonferroni correction across features and the generalized Berk–Jones statistic, which needs the covariance $\Sigma$ of the single-tissue statistics, estimated as $W \Sigma_{s,s} W^{\mathsf T}$ with $W$ the matrix of per-tissue expression weights.

## Depends on

- [Sparse canonical correlation features for cross-tissue expression](sparse-canonical-correlation-features-for-cross-tissue-expression.md)

## Expansion

The point of the Cauchy combination is that the tail of a weighted sum of Cauchy variables is asymptotically the same whether or not the summands are independent, so no covariance of the combined $p$-values has to be estimated — an advantage here because the cross-tissue features and the single-tissue features are strongly correlated by construction and their joint covariance is not available from summary statistics. The combination also matters because the two kinds of feature win in different regimes: cross-tissue features help when the genetic component of expression is shared and per-tissue sample sizes are small, single-tissue features when the causal tissue's genetic component is idiosyncratic. The elastic net is fitted on all cis-SNPs rather than only those with nonzero sCCA weight, since the sparse weights serve to define the expression feature, not to select predictors.

## Sources

- H. Feng, N. Mancuso, A. Gusev, A. Majumdar, M. Major, B. Pasaniuc and P. Kraft, "Leveraging expression from multiple tissues using sparse canonical correlation analysis and aggregate tests improves the power of transcriptome-wide association studies", PLoS Genetics 17 (2021), e1008973, Methods ("TWAS", "sCCA-TWAS", "Combined test with sCCA-features and single-tissue features"), <https://doi.org/10.1371/journal.pgen.1008973>, PMCID PMC8057593.
- Y. Liu and J. Xie, "Cauchy combination test: a powerful test with analytic p-value calculation under arbitrary dependency structures", Journal of the American Statistical Association 115 (2020), 393–402, <https://doi.org/10.1080/01621459.2018.1554485>.
