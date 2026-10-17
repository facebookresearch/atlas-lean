---
article_id: af_3619f4c7bbaaa801a759806a
declaration: def
origin: cited
statement: formalized
lean: Nat.threeSquareRepresentationCount
---

# Three Square Representation Count

`threeSquareRepresentationCount n` counts ordered triples `(x, y, z)` with
   `x, y, z ∈ [-(n : ℤ), n]` and `x ^ 2 + y ^ 2 + z ^ 2 = n`. The interval
   `[-(n : ℤ), n]` contains every integer solution and handles `n = 0`, so
   this realizes the exact source count `r₃(n)`.
   Primary source: E. T. Mortenson, arXiv:1702.01627v2,
   `Mortenson-AC-Gauss-arxiv-v2.tex` lines 127-131 (span SHA-256
   `2f2704bfc2f61e5fc50b27df3e14542a0ef19ddd4c7580c7f589f23d38ccff12`,
   file SHA-256 `13bccb58b9397a2bf3fb713779f0d76623513aec5c0f313a3cf95cf8466b5cf3`)
   defining `rₛ` by `Rₛ(q) = ∑ₙ rₛ(n) (-q) ^ n = (∑_{m ∈ ℤ} (-1) ^ m q ^ (m ^ 2)) ^ s`
   (ordered signed integer tuples). Ranked source arXiv:2307.05244 `main.tex`
   lines 78-82 (span SHA-256 `08a4b80a1e84386e7dc97f8d87e1a4f84945d55022722618d59beca2382f9942`)
   identifies the equation `x ^ 2 + y ^ 2 + z ^ 2 = n`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.QuadraticForms.ThreeSquares](../../../../../../sources/v2/MathlibExt.md)
