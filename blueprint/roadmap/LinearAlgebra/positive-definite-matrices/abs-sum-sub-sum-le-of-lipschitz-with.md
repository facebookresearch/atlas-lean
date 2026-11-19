# Lipschitz linear statistics of Hermitian spectra are stable

Let $A$ and $B$ be Hermitian $n \times n$ complex matrices with eigenvalues
$\lambda_1(A), \dots, \lambda_n(A)$ and $\lambda_1(B), \dots, \lambda_n(B)$, listed with
multiplicity in any order, and let $f : \mathbb{R} \to \mathbb{R}$ be $L$-Lipschitz. Then

$$\Big| \sum_{i=1}^n f(\lambda_i(A)) - \sum_{i=1}^n f(\lambda_i(B)) \Big| \le L \sqrt{n}
\Big( \sum_{i=1}^n \sum_{j=1}^n |A_{ij} - B_{ij}|^2 \Big)^{1/2}.$$

For $n \ge 1$, dividing by $n$: the integral of $f$ against the empirical spectral distribution moves by at most
$L \|A - B\|_F / \sqrt{n}$, where $\|\cdot\|_F$ is the Frobenius norm. In random matrix theory this
is how a matrix is compared with a perturbation of it, for instance to reduce Wigner's semicircle
law to bounded entries by truncation.

Proof: sort both spectra in decreasing order, bound each term by $L|\lambda_i(A) - \lambda_i(B)|$,
apply Cauchy–Schwarz, and conclude with the Hoffman–Wielandt inequality.

## Informally uses

- [Hoffman–Wielandt inequality for Hermitian matrices](hoffman-wielandt-hermitian.md): the final
  step, $\sum_i (\lambda_i(A) - \lambda_i(B))^2 \le \|A - B\|_F^2$.

## Background

- [Wigner's semicircle law](../../Probability/high-dimensional-probability/wigner-s-semicircle-law/wigner-semicircle.md):
  background; the truncation step of its proof uses this estimate.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §1.3, inequality (1.68), and §2.4.1, Lemma 2.4.3 (the distribution-function form of this
  estimate); the statement here is its linear-statistics variant.
