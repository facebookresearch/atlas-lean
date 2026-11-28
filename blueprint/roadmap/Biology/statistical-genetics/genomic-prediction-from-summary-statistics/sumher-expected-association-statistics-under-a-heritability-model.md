# SumHer: expected association statistics under an annotation-based heritability model

**Heritability model.** For SNPs $j = 1, \dots, m$ with pre-specified annotations $a_{j1}, \dots, a_{jK}$, the expected heritability contributed by SNP $j$ is

$$\mathbb{E}[h_j^2] = a_{j1}\tau_1 + a_{j2}\tau_2 + \dots + a_{jK}\tau_K,$$

with unknown parameters $\tau_1, \dots, \tau_K$. Examples: the one-parameter GCTA Model ($\mathbb{E}[h_j^2]$ constant), the one-parameter LDAK-Thin Model (depending on minor allele frequency and local linkage disequilibrium), and the 66-parameter BLD-LDAK Model (adding functional annotations).

**Expected test statistics.** For single-SNP association $\chi^2$ statistics $S_j$ from $n$ individuals, and squared correlations $c_{jl}^2$ between SNPs $j$ and $l$ in a reference panel,

$$\mathbb{E}[S_j] \approx 1 + n\sum_{l} c_{jl}^2\big(a_{l1}\tau_1 + a_{l2}\tau_2 + \dots + a_{lK}\tau_K\big),$$

where the sum runs over SNPs near $j$ (for example within 1 cM). SumHer estimates $\tau$ by regressing the observed $S_j$ on $\mathbb{E}[S_j]$ and reports per-SNP estimates $e_j$ of $\mathbb{E}[h_j^2]$ by plugging $\hat\tau$ into the model; total SNP heritability is $\sum_j e_j$.

## Proof sketch

Under a linear model with effects $\beta_l$ of variance $\mathbb{E}[h_l^2]$ (standardized genotypes and phenotype), the marginal regression coefficient of SNP $j$ is $\sum_l r_{jl}\beta_l$ plus noise of variance $1/n$, so $\mathbb{E}[S_j] = n\,\mathbb{E}[\hat\beta_j^2] \approx 1 + n\sum_l r_{jl}^2\,\mathbb{E}[h_l^2]$. With constant $\mathbb{E}[h_l^2] = h^2/m$ this is [LD-score regression](../ld-score-regression/model.md), where $\sum_l r_{jl}^2$ is the LD score; the annotation model replaces the constant by a linear predictor, which makes $\mathbb{E}[S_j]$ linear in $\tau$. Alternative models are compared by the Akaike information criterion $2K - 2\log l$ of the approximate likelihood. An optional extra parameter can absorb inflation from population structure, but the source no longer recommends it when the estimates are used to build prediction models.

## Sources

- Q. Zhang, F. Privé, B. Vilhjálmsson and D. Speed, "Improved genetic prediction of complex traits from individual-level data or summary statistics", Nature Communications 12 (2021), 4192, Methods ("Heritability models", Equations (2) and (3)), <https://doi.org/10.1038/s41467-021-24485-y>, PMCID PMC8263809.
