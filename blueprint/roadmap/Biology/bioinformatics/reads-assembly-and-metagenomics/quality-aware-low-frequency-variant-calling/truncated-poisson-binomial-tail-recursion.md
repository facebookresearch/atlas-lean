# Truncated Poisson-binomial tail recursion

Let $p_1, \dots, p_N \in [0, 1]$ be the error probabilities of the
[Poisson-binomial null for variant bases](poisson-binomial-null-for-variant-bases-from-base-qualities.md),
fix an observed count $K \ge 1$, and write $\pi_n$ and $S_n = T_K(p_1, \dots, p_n)$ for the
[Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md) and
[upper tail](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail.md) of the first $n$ trials. By the
[tail after adding a trial](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail-cons-succ.md), applied with $a = p_n$,
$q = (p_1, \dots, p_{n-1})$ and $k = K - 1$ (the law does not depend on the order of the trials),

$$S_n = S_{n-1} + p_n\, \pi_{n-1}(K - 1), \qquad S_0 = 0 .$$

**Algorithm and its cost.** The tail $p$-value $S_N$ is therefore computed by updating only the
masses $\pi_n(k)$ with $k < K$, each by the
[first-step recurrence](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-succ.md), and accumulating $S_n$; this takes
$O(KN)$ arithmetic operations instead of the $O(N^2)$ of the full mass function. Since every increment
$p_n \pi_{n-1}(K-1)$ is nonnegative, $S_n$ is nondecreasing in $n$, so if $S_n > t$ for some $n \le N$
then $S_N > t$, and the computation can stop as soon as the partial tail exceeds the significance
threshold $t$.

## Depends on

- [Poisson-binomial null for variant bases from base qualities](poisson-binomial-null-for-variant-bases-from-base-qualities.md)
- [Upper tail of the Poisson-binomial law](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail.md)

## Proof depends on

- [Poisson-binomial tail after adding a trial](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail-cons-succ.md)
- [First-step recurrence for the Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-succ.md)
- [Nonnegativity of the Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-nonneg.md)

## Remarks

Together the recursion and the early stop make variant calling cheap on real data, where almost every
alignment column has few or no non-reference bases: $K$ is small, and the partial tail crosses the
threshold after a few bases, so most columns are dismissed early. Probabilities are kept in log space,
with $\log(a + b) = \log a + \log\bigl(1 + e^{\log b - \log a}\bigr)$ for $a > b$, to preserve precision
at coverages of tens of thousands.

## Sources

- A. Wilm, P. P. Aw, D. Bertrand, G. H. Yeo, S. H. Ong, C. H. Wong, C. C. Khor, R. Petric,
  M. L. Hibberd, N. Nagarajan, "LoFreq: a sequence-quality aware, ultra-sensitive variant caller for
  uncovering cell-population heterogeneity from high-throughput sequencing datasets", Nucleic Acids
  Research 40 (2012) 11189-11201, Materials and Methods, "Runtime optimization", Eq. (2),
  <https://doi.org/10.1093/nar/gks918> (PMC3526318).
