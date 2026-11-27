# Poisson-binomial null for variant bases from base qualities

Consider one column of a read alignment against a consensus reference, containing $N$ bases. Base $n$
has a [Phred quality score](../quality-aware-paired-end-read-merging/phred-quality-score-and-base-call-error-probability.md) $Q_n$, so the probability that its call is an error is

$$p_n = 10^{-Q_n/10} \in (0, 1].$$

Under the null hypothesis that the column carries no true variant, each base is an independent
Bernoulli trial that shows a non-reference base exactly when it is a sequencing error, with
probability $p_n$. The number $K$ of variant bases in the column is then a
[sum of independent Bernoulli variables](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/bernoulli-sum-pmf.md), with the
[Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md) $\pi_p$ of $p = (p_1, \dots, p_N)$. The
caller computes $\pi_p$ by adding one base at a time with the
[first-step recurrence](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-succ.md)
$\pi_{(a,q)}(j+1) = a\, \pi_q(j) + (1-a)\, \pi_q(j+1)$ and the
[zero case](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-zero.md) $\pi_{(a,q)}(0) = (1-a)\,\pi_q(0)$, starting from the
empty vector, whose mass is $1$ at $0$. A variant is called when the exact upper-tail $p$-value of
the observed count $K$,

$$P = T_K(p) = \sum_{j \ge K} \pi_p(j),$$

the [Poisson-binomial upper tail](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail.md), which equals
[the probability of at least $K$ errors](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/measure-le-sum-eq-poisson-binomial-tail.md) under the null,
is below a threshold corrected for the number of tests. Variant bases with quality below a threshold
$T$ (default $Q20$) are discarded, and the remaining variant bases are assigned quality $T$, so that a
few overconfident calls cannot drive significance.

## Depends on

- [Phred quality score and base-call error probability](../quality-aware-paired-end-read-merging/phred-quality-score-and-base-call-error-probability.md)
- [Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md)
- [Upper tail of the Poisson-binomial law](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-tail.md)

## Proof depends on

- [Distribution of a sum of independent Bernoulli variables](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/bernoulli-sum-pmf.md)
- [First-step recurrence for the Poisson-binomial mass function](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-succ.md)
- [Poisson-binomial mass at zero after adding a trial](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf-cons-zero.md)
- [Tail of a sum of independent Bernoulli variables is Poisson-binomial](../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/measure-le-sum-eq-poisson-binomial-tail.md)

## Remarks

A binomial null with one average error rate is miscalibrated when base qualities vary along reads and
across reads, and in deep data that variation decides whether a variant at 0.1% frequency can be
distinguished from noise. Using each base's own error probability makes the test adapt automatically
to coverage and quality. Adding the $N$ bases one at a time computes the whole mass function in
$O(N^2)$ time. When qualities are missing or unreliable, the $12$ substitution-specific error rates
can instead be estimated by expectation-maximization over columns, alternately calling variants with
a binomial test and re-estimating the error rates from the columns that are not called.

## Sources

- A. Wilm, P. P. Aw, D. Bertrand, G. H. Yeo, S. H. Ong, C. H. Wong, C. C. Khor, R. Petric,
  M. L. Hibberd, N. Nagarajan, "LoFreq: a sequence-quality aware, ultra-sensitive variant caller for
  uncovering cell-population heterogeneity from high-throughput sequencing datasets", Nucleic Acids
  Research 40 (2012) 11189-11201, Materials and Methods, "Modeling sequencing error", Eq. (1), and
  "Sequencing quality", <https://doi.org/10.1093/nar/gks918> (PMC3526318).
