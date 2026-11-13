# Perfect covers of a cyclic 2-group times a cyclic group of order 2, 4 or 8

Write
$C(K)$ for the number of perfect covers of a group $K$. For every $n \ge 0$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_2) = 2^{n-1} \, 2^{n(n-1)/2} \, (n + 2)$, where $2^{n-1}$
is an integer power of $2$ (equal to $1/2$ at $n = 0$). For every $n \ge 1$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_4) = 2^{2n-2} \, 2^{n(n-1)/2} \, (n^2 + 11n + 4)$.
For every $n \ge 2$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_8) =
2^{3n-3} \, 2^{n(n-1)/2} \, (4n^3 + 108n^2 + 512n - 384)/3$.

## Sources

- John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 25 (`jis-2025-25.7.8-cor-25`). The record gives no range; the second identity fails at `n = 0` (`C(ℤ₄) = 2`, formula `1`) and the third at `n = 0, 1` (`C(ℤ₈) = 8`, formula `-16`; `C(ℤ₂ ⊕ ℤ₈) = 160`, formula `80`), matching Theorem 3's range `m ≥ n`.
