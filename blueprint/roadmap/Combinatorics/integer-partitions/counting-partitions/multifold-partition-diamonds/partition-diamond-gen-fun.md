# Product formula for equal-fold partition diamonds

Let $d$ and $M$ be positive integers.
Let $\sigma_{d,M}(a, b)$ be the generating function of multifold partition diamonds of shape
$(d, \dots, d)$ ($M$ copies), where $a$ marks the fold sum and $b$ marks the link sum, and let
$E_d(x, y) = \sum_{\tau} x^{\mathrm{des}(\tau)} y^{\mathrm{maj}(\tau)}$ be the Euler–Mahonian
polynomial, summed over the permutations $\tau$ of $\{1, \dots, d\}$. Then the following
identity holds in $\mathbb{Z}[[a, b]]$:

$$\left(1 - a^{Md} b^{M+1}\right) \prod_{n=1}^{M} \prod_{j=0}^{d} \left(1 - a^{nd-j} b^{n}\right)
\cdot \sigma_{d,M}(a, b) = \prod_{n=1}^{M} E_d\left(a^{(n-1)d} b^{n}, a\right).$$

Equivalently, $\sigma_{d,M}(a, b)$ is the product of the $E_d(a^{(n-1)d} b^n, a)$ divided by
$(1 - a^{Md} b^{M+1}) \prod_{n=1}^{M} \prod_{j=0}^{d} (1 - a^{nd-j} b^n)$.

## Sources

- Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds Revisited*, INTEGERS 26 (2026), Article A13, Theorem 2.
