# Broad-sense heritability from one-way ANOVA of clonal groups

Let $a \ge 2$ genotypes be observed, genotype $i$ in $n_i \ge 2$ independent hosts, $N = \sum_i n_i$, and let the phenotype follow the one-way random-effects model

$$y_{ij} \;=\; \mu + g_i + e_{ij}, \qquad i = 1, \dots, a,\ j = 1, \dots, n_i,$$

with all $g_i$ and $e_{ij}$ mutually independent, $\mathbb{E} g_i = \mathbb{E} e_{ij} = 0$, $\operatorname{Var} g_i = \sigma_g^2$ (genetic) and $\operatorname{Var} e_{ij} = \sigma_e^2$ (host and environment). With group means $\bar y_i$ and grand mean $\bar y = N^{-1}\sum_{i,j} y_{ij}$, define

$$MS_B = \frac{\sum_i n_i(\bar y_i - \bar y)^2}{a - 1}, \qquad MS_W = \frac{\sum_{i,j}(y_{ij} - \bar y_i)^2}{N - a}, \qquad n_0 = \frac{1}{a-1}\Bigl(N - \frac{\sum_i n_i^2}{N}\Bigr).$$

Then $\mathbb{E}[MS_W] = \sigma_e^2$ and $\mathbb{E}[MS_B] = \sigma_e^2 + n_0\sigma_g^2$, so $\hat\sigma_g^2 = (MS_B - MS_W)/n_0$ and $\hat\sigma_e^2 = MS_W$ are unbiased, and the broad-sense heritability $H^2 = \sigma_g^2/(\sigma_g^2 + \sigma_e^2)$ is estimated by

$$\hat H^2 \;=\; \frac{MS_B - MS_W}{MS_B + (n_0 - 1)\,MS_W} .$$

For balanced groups ($n_i = n$), $n_0 = n$ and $\hat H^2$ is the ANOVA intraclass correlation.

## Depends on

- [Intraclass correlation](../../../Probability/linear-models-multivariate/random-intercept-models-and-the-design-effect/icc.md)

## Expansion

Within group $i$, $\sum_j (y_{ij} - \bar y_i)^2$ has expectation $(n_i - 1)\sigma_e^2$, which gives $\mathbb{E}[MS_W]$. For the between-group sum of squares, write $\bar y_i - \bar y = (g_i - \bar g_w) + (\bar e_i - \bar e)$ with $\bar g_w = N^{-1}\sum_i n_i g_i$. A direct computation gives $\mathbb{E}\sum_i n_i(g_i - \bar g_w)^2 = \sigma_g^2(N - \sum_i n_i^2/N)$ and $\mathbb{E}\sum_i n_i(\bar e_i - \bar e)^2 = (a-1)\sigma_e^2$, hence $\mathbb{E}[MS_B] = \sigma_e^2 + n_0\sigma_g^2$. Substituting the unbiased component estimates into $H^2$ gives the displayed ratio, which is consistent but not unbiased, and can be negative when $MS_B < MS_W$. Clonal parasite genotypes infecting several patients act as identical twins reared apart: the same genome is expressed in different hosts. Applied to the log parasite clearance half-life of artemisinin-treated malaria on the Thailand–Myanmar border, after regressing out patient covariates, this estimator gave a heritability that rose from $32\%$ (2001–2004) to $58\%$ (2007–2010), consistent with spreading resistance alleles.

## Sources

- A. P. Phyo, S. Nkhoma, K. Stepniewska, E. A. Ashley, S. Nair, R. McGready, et al., "Emergence of artemisinin-resistant malaria on the western border of Thailand: a longitudinal study", *The Lancet* 379(9830) (2012) 1960–1966, Methods ("Statistical analysis": heritability "estimated from the mean squares terms in ANOVA") and Discussion, <https://doi.org/10.1016/S0140-6736(12)60484-X> (PMC3525980). The source does not give the estimator; the form above, with $n_0$ for unequal group sizes, is the standard one-way random-effects estimator.
- S. R. Searle, G. Casella, C. E. McCulloch, *Variance Components*, Wiley (1992), Chapter 3, the unbalanced one-way classification (expected mean squares and the coefficient $n_0$), <https://doi.org/10.1002/9780470316856>.
