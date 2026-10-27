---
article_id: af_3fdbf1f938f997766c952568
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.oesper_weaving_three_determinant
---

# Oesper Weaving Determinant

Oesper's determinant formula for the three-strand weaving knot
`W(k, 3) = S(3, k, (1, -1))`: the knot determinant equals
`-(C (2 * k - 2) + 1) * C (2 * k) + C (2 * k - 1) ^ 2` where
`C j = ∑ i ∈ Finset.Icc 1 j, (-1 : ℤ) ^ (i + 1) * Nat.fib i`.

The JIS base-word matrix is `M = !![2, -1, 0; 0, 0, 1; -1, 0, 2]` for
`S(3, k, (1, -1))`; the knot determinant is the absolute determinant of the
minor of `M ^ k - 1` deleting zero-based row 0 and column 0. Cofactor minors
of `M ^ k - 1` differ by sign, so the fixed minor is wrapped in `abs` to give
the nonnegative knot determinant.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.OesperWeavingDeterminant](../../../../../../sources/v2/MathlibExt.md)
- Seong Ju Kim, Ryan Stees, and Laura Taalman, "Sequences of Spiral Knot Determinants", Journal of Integer Sequences 19 (2016), Article 16.1.4, lines 409-412: https://cs.uwaterloo.ca/journals/JIS/VOL19/Stees/stees4.tex The formula is attributed to L. Oesper, "p-colorings of weaving knots" (preprint). Proves `Wanted` entry `oesper_weaving_three_determinant`.
