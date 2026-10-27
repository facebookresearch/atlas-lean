---
article_id: af_9e0e30fbe4e1f5d636d4a68b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.rStirlingFirst_eq_alternating_sum
---

# R Stirling First eq alternating sum

Broder's expansion formula for r-Stirling numbers of the first kind.

Equation (43): `(-1)^r [n,m]_r = ∑ k, [n,m-r+k] {k-1,r-1} (-1)^k`,
for `n ≥ r ≥ 1`, where square brackets are unsigned first-kind Stirling
numbers and braces are second-kind Stirling numbers.

Finite support and index encoding: the second-kind factor vanishes below
`k = r`, and the first-kind factor vanishes above `k = n + r - m`, so the
sum is over `Finset.Icc r (n + r - m)`; for `k ≥ r` the source index
`m - r + k` is represented without truncation as `m + (k - r)`.
Natural coefficients are cast to `Int` so the alternating signs are exact.

## Depends on

- [R Stirling First](r-stirling-first.md)

## Proof depends on

- [R Stirling First self](r-stirling-first-self.md)
- [R Stirling First succ](r-stirling-first-succ.md)
- [R Stirling First zero of pos](r-stirling-first-zero-of-pos.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion](../../../../../../../sources/v2/MathlibExt.md)
- A. Z. Broder, "The r-Stirling numbers", Stanford Computer Science Report STAN-CS-82-949 (December 1982), PDF page 16 / printed page 13, Equation (43); journal version: Discrete Mathematics 49 (1984), 241-259, DOI 10.1016/0012-365X(84)90161-4.
