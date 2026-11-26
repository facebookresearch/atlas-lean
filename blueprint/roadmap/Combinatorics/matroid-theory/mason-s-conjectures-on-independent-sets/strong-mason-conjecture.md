# The strong Mason conjecture

Let $M$ be a finite matroid whose ground set has $n$
elements, and for each $j$ let $I_j$ be the number of independent sets of $M$ with $j$ elements.
Then for every natural number $k$ with $0 < k < n$,

$$I_{k-1} \, I_{k+1} \, (k+1) \, (n-k+1) \le I_k^2 \, k \, (n-k).$$

Equivalently, the sequence $I_k / \binom{n}{k}$ is log-concave for $0 \le k \le n$.

## Informally uses

- [Independence generating polynomials of matroids are Lorentzian](../lorentzian-polynomials/independence-generating-polynomial-mem-l.md):
  Brändén and Huh's proof of Theorem 4.14 starts from the Lorentzian property of
  $\sum_{A} w^A w_0^{n-|A|}$.
- [Nonnegative linear changes of variables preserve Lorentzian polynomials](../lorentzian-polynomials/mem-l-comp-nonneg.md):
  it then sets $w_1 = \cdots = w_n$ (Theorem 2.10).
- [Bivariate Lorentzian polynomials](../lorentzian-polynomials/bivariate-mem-l-iff.md): the
  resulting bivariate Lorentzian polynomial has ultra log-concave coefficients $I_k$.

## Sources

- P. Branden and J. Huh, 'Lorentzian polynomials', Ann. of Math. 192 (2020), 821-891, Theorem 4.14, https://doi.org/10.4007/annals.2020.192.3.4; independently N. Anari, K. Liu, S. Oveis Gharan, and C. Vinzant, 'Log-concave polynomials III: Mason's ultra-log-concavity conjecture for independent sets of matroids', https://arxiv.org/abs/1811.01600. Problem `strong_mason_conjecture` of the lean-eval benchmark.
