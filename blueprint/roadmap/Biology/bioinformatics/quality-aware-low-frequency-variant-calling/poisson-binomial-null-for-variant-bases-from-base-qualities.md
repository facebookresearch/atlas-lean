# Poisson-binomial null for variant bases from base qualities

Consider one column of a read alignment against a consensus reference, containing $N$ bases. Base $n$
has a Phred-scaled quality $Q_n$, which encodes the probability that the base call is an error,

$$p_n = 10^{-Q_n/10} \in (0, 1).$$

Under the null hypothesis that the column carries no true variant, each base is an independent
Bernoulli trial that shows a non-reference base exactly when it is a sequencing error, with
probability $p_n$. The number $K$ of variant bases in the column then has the Poisson-binomial
distribution with parameters $(p_1, \dots, p_N)$. Its probability mass function is computed by the
recursion

$$\Pr\nolimits_n(X = k) = (1 - p_n)\Pr\nolimits_{n-1}(X = k) + p_n \Pr\nolimits_{n-1}(X = k - 1),$$

for $n = 1, \dots, N$, with $\Pr_0(X = 0) = 1$ and $\Pr_{n}(X = k) = 0$ for $k < 0$ or $k > n$, where
$\Pr_n$ is the law of the number of errors among the first $n$ bases. A variant is called when the
exact upper-tail $p$-value

$$P = \sum_{k \ge K} \Pr\nolimits_N(X = k)$$

is below a threshold corrected for the number of tests. Variant bases with quality below a threshold
$T$ (default $Q20$) are discarded, and the remaining variant bases are assigned quality $T$, so that a
few overconfident calls cannot drive significance.

## Expansion

A binomial null with one average error rate is miscalibrated when base qualities vary along reads and
across reads, and in deep data that variation decides whether a variant at 0.1% frequency can be
distinguished from noise. Using each base's own error probability makes the test adapt automatically
to coverage and quality. The recursion follows from conditioning on whether base $n$ is an error, and
it computes the whole pmf in $O(N^2)$ time. When qualities are missing or unreliable, the $12$
substitution-specific error rates can instead be estimated by expectation-maximization over columns,
alternately calling variants with a binomial test and re-estimating the error rates from the columns
that are not called.

## Sources

- A. Wilm, P. P. Aw, D. Bertrand, G. H. Yeo, S. H. Ong, C. H. Wong, C. C. Khor, R. Petric,
  M. L. Hibberd, N. Nagarajan, "LoFreq: a sequence-quality aware, ultra-sensitive variant caller for
  uncovering cell-population heterogeneity from high-throughput sequencing datasets", Nucleic Acids
  Research 40 (2012) 11189-11201, Materials and Methods, "Modeling sequencing error", Eq. (1), and
  "Sequencing quality", <https://doi.org/10.1093/nar/gks918> (PMC3526318).
