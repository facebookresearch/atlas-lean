# Truncated Poisson-binomial tail recursion

Let $p_1, \dots, p_N \in [0, 1]$, let $X_n$ be the number of successes among the first $n$ of the
corresponding independent Bernoulli trials, and fix an observed count $K \ge 1$. Write
$\Pr_n(k) = \Pr(X_n = k)$ and $S_n = \Pr(X_n \ge K)$. Then, for $n \ge 1$,

$$S_n = S_{n-1} + p_n \Pr\nolimits_{n-1}(K - 1), \qquad S_0 = 0,$$

so the tail $p$-value $S_N$ can be computed while keeping only the entries $\Pr_n(k)$ with $k < K$,
each updated by the
[Poisson-binomial recursion](poisson-binomial-null-for-variant-bases-from-base-qualities.md),
in $O(KN)$ time instead of $O(N^2)$. Moreover $S_n$ is nondecreasing in $n$: if $S_n > t$ for some
$n \le N$, then $S_N > t$, and the computation can stop as soon as the partial tail exceeds the
significance threshold $t$.

## Depends on

- [Poisson-binomial null for variant bases from base qualities](poisson-binomial-null-for-variant-bases-from-base-qualities.md)

## Expansion

The event $\{X_n \ge K\}$ is the union of $\{X_{n-1} \ge K\}$ and the disjoint event that
$X_{n-1} = K - 1$ and trial $n$ succeeds, which gives the recursion. Monotonicity is immediate,
since $X_n \le X_{n+1}$ pathwise. Together they make variant calling cheap on real data, where almost
every alignment column has few or no non-reference bases: $K$ is small, and the partial tail crosses
the threshold after a few bases, so most columns are dismissed early. Probabilities are kept in log
space, with $\log(a + b) = \log a + \log\bigl(1 + e^{\log b - \log a}\bigr)$ for $a > b$, to preserve
precision at coverages of tens of thousands.

## Sources

- A. Wilm, P. P. Aw, D. Bertrand, G. H. Yeo, S. H. Ong, C. H. Wong, C. C. Khor, R. Petric,
  M. L. Hibberd, N. Nagarajan, "LoFreq: a sequence-quality aware, ultra-sensitive variant caller for
  uncovering cell-population heterogeneity from high-throughput sequencing datasets", Nucleic Acids
  Research 40 (2012) 11189-11201, Materials and Methods, "Runtime optimization", Eq. (2),
  <https://doi.org/10.1093/nar/gks918> (PMC3526318).
