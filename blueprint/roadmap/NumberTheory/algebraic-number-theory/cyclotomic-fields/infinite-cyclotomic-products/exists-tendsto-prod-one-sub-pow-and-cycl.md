# A zeta-twisted cyclotomic product identity

For $n \ge 1$ and complex $z$, let
$\hat\Phi_n(z) = \prod_\omega (1 - z\omega)$, the product over the primitive $n$-th roots of
unity $\omega$. Let $z$ be a complex number with $|z| < 1$, let $s > 1$ be real, and let
$\zeta$ be the Riemann zeta function. Then

$$
\prod_{i \ge 1} (1 - z^i)^{-1/i^s} = \prod_{i \ge 1} \hat\Phi_i(z)^{-\zeta(s)/i^s}
$$

in the sense that, as $N \to \infty$, the partial products over $1 \le i \le N$ of both sides
converge to a common limit. Here $(1 - z^i)^{-1/i^s} = \exp(-i^{-s} \log(1 - z^i))$ and
$\hat\Phi_i(z)^{-\zeta(s)/i^s} = \exp(-\zeta(s) \, i^{-s} \sum_\omega \log(1 - z\omega))$, where
$\log$ is the principal branch of the logarithm.

The exponent $-\zeta(s)/i^s$ follows arXiv:2511.16975, Theorem 2.2. The INTEGERS record shows
$-\zeta(s)/i$; with that exponent the right side would equal $1$ by the constancy of
$\prod_{n \ge 1} \hat\Phi_n(z)^{-1/n}$, while the left side does not.

## Sources

- Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*, INTEGERS 25 (2025), Article A96, Theorem 2 (`integers-2025-A96-thm-2`).
