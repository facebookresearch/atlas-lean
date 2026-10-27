---
article_id: af_813942e28e9ebdca94207882
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.legendre_regular_crossing
---

# Complete Bipartite Crossing

The left side counts distinct interior intersection points of the regular drawing with left
vertices `(0, i)` and right vertices `(1, j)` in `Rat × Rat` for `i, j < n`: edges cross in the
interior exactly when `i < i'` and `j' < j`, the image point is the explicit segment intersection,
and `Finset.card` counts distinct points. The right side is the paper formula: the sum over `1 ≤ a,
b ≤ n - 1` with `Nat.Coprime a b` of `(n - a) * (n - b)` minus the correction sum over
`1 ≤ 2 * a, 2 * b ≤ n - 1` with `Nat.Coprime a b` of `(n - 2 * a) * (n - 2 * b)`, with bounds
encoded by
`Finset.range` and filters so subtraction stays in `ℕ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Graph.CompleteBipartiteCrossing](../../../../../sources/v2/MathlibExt.md)
- Stéphane Legendre, "The Number of Crossings in a Regular Drawing of the Complete Bipartite Graph", Journal of Integer Sequences 12 (2009), Article 09.5.5, Proposition `count_all`, line 263, <https://cs.uwaterloo.ca/journals/JIS/VOL12/Legendre/legendre2.tex>.
