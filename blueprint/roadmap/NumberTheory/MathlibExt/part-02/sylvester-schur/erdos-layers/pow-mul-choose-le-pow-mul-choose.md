---
article_id: af_5bf34c9fe7e0cd0843173123
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Nat.SylvesterSchur.pow_mul_choose_le_pow_mul_choose
---

# Pow mul choose le pow mul choose

Scaled monotonicity for binomial coefficients:
`N^r * (M choose r) ≤ M^r * (N choose r)` for `r ≤ M ≤ N`.

Equivalently, `(Nat.choose N r : ℚ) / N^r` is monotone decreasing in this range.
This form stays in `ℕ`, avoiding division.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.SylvesterSchur.ErdosLayers](../../../../../../sources/v2/MathlibExt.md)
