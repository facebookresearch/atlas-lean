# Product formula for multifold partition diamonds

Let $d_1, \dots, d_M$ be positive
integers with $M \ge 1$, and let $\omega_k = \sum_{m=k+1}^{M} d_m$ for $0 \le k \le M$. Let
$\sigma_{d_1, \dots, d_M}(a, b)$ be the generating function of multifold partition diamonds of
shape $(d_1, \dots, d_M)$, where $a$ marks the fold sum and $b$ marks the link sum, and let
$E_d(x, y) = \sum_{\tau} x^{\mathrm{des}(\tau)} y^{\mathrm{maj}(\tau)}$ be the Euler–Mahonian
polynomial, summed over the permutations $\tau$ of $\{1, \dots, d\}$. Then the following
identity holds in $\mathbb{Z}[[a, b]]$:

$$\left(1 - a^{\omega_0} b^{M+1}\right) \prod_{k=1}^{M} \prod_{j=0}^{d_k}
\left(1 - a^{\omega_k + d_k - j} b^{M-k+1}\right) \cdot \sigma_{d_1, \dots, d_M}(a, b) =
\prod_{k=1}^{M} E_{d_k}\left(a^{\omega_k} b^{M-k+1}, a\right).$$

The $k$th diamond (with $d_k$ folds) is the $k$th from the smallest part, as in the paper's poset
$\{1\} \oplus Q_{d_1} \oplus \dots \oplus Q_{d_M}$. If the parts are read in the opposite order,
the formula holds only for the reversed sequence: for $(d_1, d_2) = (1, 2)$ the coefficient of
$ab$ would be $1$, not $2$.

## Sources

- Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds Revisited*, INTEGERS 26 (2026), Article A13, Theorem 3 (`integers-2026-A13-thm-3`).
