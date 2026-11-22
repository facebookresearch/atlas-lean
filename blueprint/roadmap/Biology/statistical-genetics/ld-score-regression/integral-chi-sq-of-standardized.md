# LD-score regression

Let an [LD-score model](model.md) on a measure $\mu$ have heritability $h^2$ and $N \ne 0$ individuals, and let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix. Then for every marker $j$,

$$\int \chi^2_j \, d\mu = \frac{N h^2}{M}\, \ell_j + (1 - h^2),$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\ell_j$ the [LD score](ld-score.md), with the convention $x/0 = 0$ when $M = 0$. The expected statistic is affine in the LD score, with slope $N h^2 / M$ and intercept $1 - h^2$; the regression equation of Bulik-Sullivan et al. (2015) has intercept $1$, an approximation valid when $h^2$ is small.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
