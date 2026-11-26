# DerSimonian–Laird random-effects meta-analysis

**Model.** In the setting of [inverse-variance meta-analysis](inverse-variance-fixed-effects-meta-analysis-and-heterogeneity.md), let the true effect differ between studies: $\beta_{ij} \mid \theta_{ij} \sim \mathcal{N}(\theta_{ij}, V_{ij})$ with $\theta_{ij} \sim \mathcal{N}(\beta_j, \tau_j^2)$ independent, so marginally $\beta_{ij} \sim \mathcal{N}(\beta_j, V_{ij} + \tau_j^2)$.

**Moment estimator of the between-study variance.** With fixed-effects weights $w_{ij} = V_{ij}^{-1}$, Cochran's $Q_j$ and $N_j$ reporting studies,

$$\hat\tau_j^2 = \max\!\left(0,\ \frac{Q_j - (N_j - 1)}{\sum_i w_{ij} - \sum_i w_{ij}^2 \big/ \sum_i w_{ij}}\right).$$

**Random-effects estimate.** With $w_{ij}^* = (V_{ij} + \hat\tau_j^2)^{-1}$,

$$\hat\beta_j^* = \frac{\sum_i w_{ij}^*\beta_{ij}}{\sum_i w_{ij}^*}, \qquad \operatorname{Var}(\hat\beta_j^*) \approx \frac{1}{\sum_i w_{ij}^*},$$

and $(\hat\beta_j^*)^2 \sum_i w_{ij}^*$ is referred to $\chi^2_1$.

## Expansion

Under the random-effects model, $\mathbb{E}Q_j = (N_j - 1) + \tau_j^2\big(\sum_i w_{ij} - \sum_i w_{ij}^2/\sum_i w_{ij}\big)$; solving for $\tau_j^2$ with $Q_j$ in place of its mean and truncating at zero gives $\hat\tau_j^2$. Adding $\hat\tau_j^2$ to every study's variance inflates the variance of the combined estimate, correcting the deflation that the fixed-effects variance shows under heterogeneity, and pulls the weights toward equality. Because the null hypothesis $\beta_j = 0$ is tested with the inflated variance even when heterogeneity arises only under the alternative, this test is conservative and is never more powerful than the fixed-effects test in GWAS settings; the Han–Eskin likelihood-ratio statistic, which keeps $\tau^2 = 0$ under the null, removes that conservativeness.

## Depends on

- [Inverse-variance fixed-effects meta-analysis and heterogeneity statistics](inverse-variance-fixed-effects-meta-analysis-and-heterogeneity.md)

## Sources

- R. Mägi and A. P. Morris, "GWAMA: software for genome-wide association meta-analysis", BMC Bioinformatics 11 (2010), 288, Implementation ("Random effects meta-analysis"), <https://doi.org/10.1186/1471-2105-11-288>, PMCID PMC2893603.
- R. DerSimonian and N. Laird, "Meta-analysis in clinical trials", Controlled Clinical Trials 7 (1986), 177–188, <https://doi.org/10.1016/0197-2456(86)90046-2>.
