# Frequency-dependent architecture

Let a [stratified LD-score model](model.md) on a measure $\mu$ have $N \ne 0$ individuals, let $p_1, \dots, p_M$, $\alpha$ and $c$ be real numbers with

$$\sigma^2_k = c\, \bigl(p_k (1 - p_k)\bigr)^{1 + \alpha}$$

for every marker $k$ (real powers; the formula is meaningful for $0 < p_k < 1$), and let $X$ be a [standardized](../ld-score-regression/is-standardized.md) real $N \times M$ genotype matrix. Then for every marker $j$,

$$\int \chi^2_j \, d\mu = N c \sum_{k=1}^{M} \bigl(p_k (1 - p_k)\bigr)^{1 + \alpha}\, r_{jk}^2 + \sigma^2_e,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $r_{jk} = \frac1N \sum_i X_{ij} X_{ik}$. With $p_k$ the allele frequency of marker $k$, this is the $\alpha$ model of Schoech et al. (2019), in which the per-allele effect variance is proportional to $(p_k(1-p_k))^{\alpha}$.

## Sources

- A. P. Schoech, D. M. Jordan, P.-R. Loh, S. Gazal, L. J. O'Connor, D. J. Balick, et al., *Quantification of frequency-dependent genetic architectures in 25 UK Biobank traits reveals action of negative selection*, Nat. Commun. 10 (2019), 790.
