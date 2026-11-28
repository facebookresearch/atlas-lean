# Consistency of the unweighted LD-score regression estimator

Let $\mu$ be a probability measure and, along a filter on an index set, let $D_n$ be
[LD-score models](model.md) under $\mu$ with $N_n \neq 0$ individuals, $M_n \neq 0$ markers, the
same heritability $h^2$, and effects and noise of mean zero; let $X_n$ be
[standardized](is-standardized.md) genotype matrices whose [LD scores](ld-score.md) are not all
equal; and let $s_n \in \mathbb{R}$ and $c_n \in \mathbb{R}^{N_n}$ be such that the stratification
term $s_n^2 (\sum_i (X_n)_{ij} c_{n,i} / N_n)^2 = a_n$ is the same for every marker $j$ of design
$n$. If the variance of the [unweighted estimator](ols-h2-hat.md) $\hat h^2_n$ of design $n$, a
value in $[0, \infty]$, tends to $0$, then $\hat h^2_n$ converges to $h^2$ in probability. The model
fixes only second moments, so the vanishing variance is a hypothesis rather than a consequence.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
