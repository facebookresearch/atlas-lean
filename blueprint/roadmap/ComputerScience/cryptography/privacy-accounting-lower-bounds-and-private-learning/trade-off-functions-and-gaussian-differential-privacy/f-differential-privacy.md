# f-differential privacy

Datasets are elements of $\mathcal{X}^n$; two datasets are neighbours if they differ in exactly one entry; a mechanism $M$ maps a dataset to a random output. Let $f$ be a trade-off function. A mechanism $M$ is **$f$-differentially private** ($f$-DP) if

$$
T\big(M(S), M(S')\big) \ge f \quad \text{for all neighbouring datasets } S, S'.
$$

Since the neighbouring relation is symmetric, $f$ may be replaced by its symmetrization, and one may assume $f$ is symmetric ($f = f^{-1}$, where $f^{-1}(\alpha) = \inf\{t : f(t) \le \alpha\}$). The definition says that no test, based on the output, of "the dataset is $S$" against "the dataset is $S'$" can have errors below the curve $f$.

## Depends on

- [Trade-off functions of pairs of distributions](trade-off-function.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../../differential-privacy/hamming-adj.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
