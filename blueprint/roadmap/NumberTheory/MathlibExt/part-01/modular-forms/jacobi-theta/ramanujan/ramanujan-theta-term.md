---
article_id: af_312e672eed0766581587da38
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.ramanujanThetaTerm
---

# Ramanujan Theta Term

The summand `a ^ (n * (n + 1) / 2) * b ^ (n * (n - 1) / 2)` in Ramanujan's
general theta function `f(a,b) = ∑' n, a ^ (n(n+1)/2) b ^ (n(n-1)/2)`.

Both integer quotients are nonnegative triangular numbers (`n(n+1)/2 ≥ 0` and
`n(n-1)/2 ≥ 0` for `n : ℤ`), so the `ℤ`-division followed by `toNat` is exact and yields the
mathematical exponent in `ℕ`. Source: the common definition in arXiv:2305.14988,
arXiv:2309.06689, arXiv:2312.15513, arXiv:2502.17312, and arXiv:2607.26471.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan](../../../../../../../sources/v2/MathlibExt.md)
