# Unbiasedness of the unweighted LD-score regression estimator

Let $\mu$ be a probability measure and $D$ an [LD-score model](model.md) under $\mu$ with $N \neq 0$
individuals, $M$ markers, heritability $h^2$, and effects $\beta_k$ and noise $\varepsilon_i$ of
mean zero. Let $X$ be a [standardized](is-standardized.md) real $N \times M$ genotype matrix with
[LD scores](ld-score.md) $\ell_j$, and let $s \in \mathbb{R}$ and $c \in \mathbb{R}^N$ be such that
the stratification term $s^2 (\sum_i X_{ij} c_i / N)^2 = a$ is the same for every marker $j$. Write
$\chi^2_j$ for the [association statistic under stratification](chi-sq-strat.md) of marker $j$.
Suppose moreover that $M \neq 0$ and that the LD scores are not all equal, that is, the spread
$S_{\ell\ell} = \sum_j (\ell_j - \bar\ell)^2$ of the LD scores is not $0$. Then the
[unweighted estimator](ols-h2-hat.md) $\hat h^2$ computed from $\ell$ and
$\chi^2_1, \dots, \chi^2_M$ satisfies $\mathbb{E}[\hat h^2] = h^2$, with or without confounding.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
