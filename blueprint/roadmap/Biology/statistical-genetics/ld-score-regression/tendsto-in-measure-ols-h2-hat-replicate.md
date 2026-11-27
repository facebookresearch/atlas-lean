# Consistency of LD-score regression along the replicated designs

Let $\nu$ be a probability measure on $\mathbb{R}$ satisfying the
[bounded unit law](is-bounded-unit-law.md) condition with bound $C$, $h^2 \in [0, 1]$, $T$ a
[standardized](is-standardized.md) real $g \times k$ template matrix whose LD scores have positive
spread $S_{\ell\ell}(T) > 0$, and, along a filter on an index set, $b_n \neq 0$ numbers of copies
with $b_n \to \infty$. Then the [unweighted estimator](ols-h2-hat.md) $\hat h^2_n$ computed from the
LD scores of the [replicated matrix](replicate.md) with $b_n$ copies and the statistics of the
[model on the product space](model-2.md) with $b_n g$ individuals and $b_n k$ markers, without
stratification, converges to $h^2$ in probability under the [product measure](coord-measure.md). The
hypotheses of [the block-design theorem](tendsto-in-measure-ols-h2-hat-block-desi.md) hold with
$\kappa = \lambda = g / k$, $c = S_{\ell\ell}(T) / k$, block size $k$ and cohort size $g$.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
