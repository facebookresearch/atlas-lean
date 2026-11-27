# Consistency of LD-score regression from fourth moments

Let $\mu$ be a probability measure and, along a filter on an index set, let $D_n$ be
[LD-score models](model.md) under $\mu$ with $N_n \neq 0$ individuals, $M_n$ markers, and effects
and noise of mean zero; let $X_n$ be [standardized](is-standardized.md) genotype matrices with
[LD scores](ld-score.md) $\ell_{n,j}$; and let $s_n \in \mathbb{R}$ and $c_n \in \mathbb{R}^{N_n}$
be such that the stratification term $s_n^2 (\sum_i (X_n)_{ij} c_{n,i} / N_n)^2 = a_n$ is the same
for every marker $j$ of design $n$. Write $\chi^2_{n,j}$ for the
[association statistics under stratification](chi-sq-strat.md). Suppose that the
[normalized scores under stratification](beta-hat-strat.md) of every design satisfy a
[score-level LD-block model](score-block-model.md) with a common block size $K$, and that there are
real numbers $\kappa_4 \geq 0$, $L$, $\lambda$, $A$, $c_0 > 0$ and $\kappa > 0$ such that for all
$n$ and $j$: $\mathbb{E}[(\chi^2_{n,j})^2] \leq \kappa_4 (\mathbb{E}[\chi^2_{n,j}])^2$,
$\ell_{n,j} \leq L$, $\kappa M_n \leq N_n \leq \lambda M_n$, $N_n a_n \leq A$, and the spread of the
LD scores satisfies $S_{\ell_n \ell_n} \geq c_0 M_n$. Suppose moreover that all models have the same
heritability $h^2$ and that $M_n \neq 0$ for every $n$. If $M_n \to \infty$, then the
[unweighted estimator](ols-h2-hat.md) $\hat h^2_n$ converges to $h^2$ in probability.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
