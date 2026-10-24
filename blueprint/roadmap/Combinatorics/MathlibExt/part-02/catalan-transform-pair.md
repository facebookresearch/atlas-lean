---
article_id: af_b9d073aab0824b77b01e95cc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_transform_pair
---

# Catalan Transform Pair

Catalan transform pair and its inverse: the double-sum formula for the
Catalan transform `b` of a sequence `a` implies two single-sum forms for `b`
(for `0 < n`) and two inversion formulas recovering `a` from `b`.

The sums range over `Finset.range (n + 1)` for both binders; terms with
`j > k` vanish since `Nat.choose k j = 0` there. The `⌊n/2⌋` bound is
`Finset.range (n / 2 + 1)`

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.CatalanTransformPair](../../../../sources/v2/MathlibExt.md)
- Paul Barry, "A Catalan Transform and Related Transformations on Integer Sequences", Journal of Integer Sequences 8 (2005), Article 05.4.5, proposition lines 302--311, <https://cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.tex>.
