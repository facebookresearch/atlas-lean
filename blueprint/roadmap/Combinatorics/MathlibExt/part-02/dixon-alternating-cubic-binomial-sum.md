---
article_id: af_9a41dffcb659ea757f1dad36
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dixon_alternating_cubic_binomial_sum
---

# Dixon Cubic Binomial

Dixon's alternating cubic binomial sum (Mikić, equation (2.0.1)): for every
nonnegative integer `n`, the alternating sum of the cubes of the binomial
coefficients `C(2n, k)` over `k = 0, ..., 2n` equals
`(-1)^n * C(2n, n) * C(3n, 2n)`.

Mikić attributes the identity to A. C. Dixon, "On the sum of the cubes of the
coefficients in a certain expansion by the binomial theorem", Messenger of
Mathematics 20 (1891), 79--80. This is the one-parameter specialization
`a = b = c = n` only; it does not state Dixon's distinct three-parameter identity.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.DixonCubicBinomial](../../../../sources/v2/MathlibExt.md)
- Jovan Mikić, "A Method For Examining Divisibility Properties Of Some Binomial Sums", Journal of Integer Sequences 21 (2018), Article 18.8.7, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Mikic/mikic25.tex>, equation (2.0.1), lines 119--124. Source file SHA-256 `6a6fc0f14a3e02c8d5cbbbb626412ac1151d9853c1ebf6ce8860b8b98d4306a2`, canonical source-span SHA-256 `8511f3d8adc6b3c69d4bcc08bd4f88b9c62c93b1ff2fd0c01dd3fe720b7df3a2`.
