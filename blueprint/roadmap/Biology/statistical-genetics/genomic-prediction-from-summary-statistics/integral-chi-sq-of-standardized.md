# Stratified LD-score regression

Let a [stratified LD-score model](stratified-model.md) on a measure $\mu$ have $N \ne 0$ individuals, categories $(C_c, \tau_c)$ and noise variance $\sigma_e^2$, and let $X$ be a real $N \times M$ genotype matrix that is standardized: every column has sum $0$ and sum of squares $N$. Then for every marker $j$ (Finucane et al. 2015),

$$\int \chi^2_j \, d\mu = N \sum_{c \in \mathcal{C}} \tau_c\, \ell(j, C_c) + \sigma_e^2,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\ell$ the [stratified LD score](strat-ldscore.md).

## Sources

- H. K. Finucane et al., *Partitioning heritability by functional annotation using genome-wide association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
