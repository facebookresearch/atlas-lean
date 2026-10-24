---
article_id: af_0359f93bfb16acca4ecff4da
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vosper_eq_iff
---

# Vosper Theorem

Vosper equality characterization: for prime `p` and nonempty
`A B : Finset (ZMod p)` with `A + B ≠ Finset.univ`,
`(A + B).card = A.card + B.card - 1` iff (i) `min A.card B.card = 1`, or
(ii) `(A + B).card = p - 1` with the complement of `A + B` equal to `{c}`
for some `c : ZMod p` and `B` the complement of the image `c - A`, or
(iii) `AreFiniteArithmeticProgressionsWithCommonDifference A B`.

## Depends on

- [Common Difference Progressions](are-finite-arithmetic-progressions-with.md)

## Proof depends on

- [Is APOf Length With](../ap/basic/is-apof-length-with.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.VosperTheorem](../../../../../sources/v2/MathlibExt.md)
- Fabián Arias, Jerson Borja, and Samuel Anaya, *Counting Integers Representable as Sums of k-th Powers Modulo n*, Journal of Integer Sequences 26 (2023), Article 23.8.1, Theorem [Vosper] `theo_Vosper`, lines 256–267, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Borja/borja4.tex>.
