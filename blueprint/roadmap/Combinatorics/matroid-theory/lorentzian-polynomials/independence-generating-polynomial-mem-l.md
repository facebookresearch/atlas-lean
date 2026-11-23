# Independence generating polynomials of matroids are Lorentzian

For a matroid $M$ whose ground set is contained in $[n]$, the homogeneous polynomial of degree $n$ in $n + 1$ variables

$$f_M(w_0, w_1, \dots, w_n) = \sum_{A \text{ independent in } M} w^A \, w_0^{\,n - |A|}$$

lies in $L^n_{n+1}$.

Brändén and Huh obtain this, in the proof of their Theorem 4.14, as the limit $q \to 0$ of
$Z_{q,M}(w_0, q w_1, \dots, q w_n)$, where $Z_{q,M}$ is the homogenised multivariate Tutte
polynomial, which is Lorentzian for $0 < q \le 1$ (Theorem 4.10). Setting
$w_1 = \cdots = w_n$ and reading off coefficients gives the strong Mason conjecture.
Anari, Liu, Oveis Gharan and Vinzant proved the same property (complete log-concavity of this
polynomial) independently (Log-concave polynomials III, Theorem 4.1).

## Sources

- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Theorem 4.10 and the proof of Theorem 4.14, https://arxiv.org/abs/1902.03719.
- N. Anari, K. Liu, S. Oveis Gharan and C. Vinzant, *Log-concave polynomials III: Mason's
  ultra-log-concavity conjecture for independent sets of matroids*, arXiv:1811.01600,
  Theorem 4.1.
