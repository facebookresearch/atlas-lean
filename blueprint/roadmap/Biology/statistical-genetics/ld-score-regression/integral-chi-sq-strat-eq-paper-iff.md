# The published regression equation holds exactly if and only if h² = 0

Let $\mu$ be a probability measure and $D$ an [LD-score model](model.md) under $\mu$ with $N \neq 0$
individuals, $M$ markers, heritability $h^2$, and effects $\beta_k$ and noise $\varepsilon_i$ of
mean zero. Let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix with
[LD scores](ld-score.md) $\ell_j$, and let $s \in \mathbb{R}$ and $c \in \mathbb{R}^N$ be such that
the stratification term $s^2 (\sum_i X_{ij} c_i / N)^2 = a$ is the same for every marker $j$. Write
$\chi^2_j$ for the [association statistic under stratification](chi-sq-strat.md) of marker $j$. Then
for every marker $j$, the regression equation of Bulik-Sullivan et al. (2015),
$\mathbb{E}[\chi^2_j] = 1 + N h^2 \ell_j / M + N a$, holds if and only if $h^2 = 0$; otherwise the
[exact identity](integral-chi-sq-strat-eq.md) differs from it by $-h^2$.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
