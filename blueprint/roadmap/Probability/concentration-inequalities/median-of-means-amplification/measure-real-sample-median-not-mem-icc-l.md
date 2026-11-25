# Median amplification

Let $\mu$ be a probability measure, $s \in \mathbb{N}$, and let $Y_1, \dots, Y_s$ be independent
measurable real random variables with $\mu(Y_i \notin [a, b]) \le 1/8$ for every $i$. Then their
[sample median](sample-median.md) satisfies

$$\mu\big(\operatorname{med}(Y_1, \dots, Y_s) \notin [a, b]\big) \le e^{-9s/32};$$

in particular it is at most $\varepsilon$ once $s \ge \frac{32}{9} \log(1/\varepsilon)$. This is the
amplification step of Alon, Matias and Szegedy, where each $Y_j$ is a mean of independent copies of
a basic estimator and Chebyshev's inequality supplies the $1/8$; the source takes
$s = 2 \log(1/\varepsilon)$ with a Chernoff bound, while this statement uses Hoeffding's inequality
and so has the explicit constant $9/32$.

## Informally uses

- [At least half of independent estimates are rarely bad](measure-real-two-mul-card-bad-ge-le.md): the probabilistic step.
- [The median lies in an interval holding a strict majority](sample-median-mem-icc.md): the deterministic step.

## Sources

- N. Alon, Y. Matias and M. Szegedy, *The space complexity of approximating the frequency
  moments*, Journal of Computer and System Sciences 58 (1999), 137–147, proofs of Theorems 2.1 and
  2.2.
