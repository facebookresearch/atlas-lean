# Summary Chi Square

The Mantel–Haenszel summary chi-square `(∑_k A_k - ∑_k E(A_k))² / ∑_k V(A_k)`, without the
continuity correction. It is meaningful when `∑_k V(A_k) > 0`; if that sum is `0`, Lean's convention
`x / 0 = 0` makes the value `0`.
