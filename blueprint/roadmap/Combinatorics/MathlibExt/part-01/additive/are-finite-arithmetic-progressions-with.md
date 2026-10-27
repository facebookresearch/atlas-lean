---
article_id: af_c8645d4d388e27340d7cb01b
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.AreFiniteArithmeticProgressionsWithCommonDifference
---

# Common Difference Progressions

Common-difference progressions: holds exactly when there is one shared
`d : G` such that `A` and `B` are both set-level arithmetic progressions of
their own cardinalities with difference `d`, stated directly with
`Set.IsAPOfLengthWith`; the two progressions may have different initial
terms and different cardinalities.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is APOf Length With](../ap/basic/is-apof-length-with.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.CommonDifferenceProgressions](../../../../../sources/v2/MathlibExt.md)
- Fabián Arias, Jerson Borja, and Samuel Anaya, *Counting Integers Representable as Sums of k-th Powers Modulo n*, Journal of Integer Sequences 26 (2023), Article 23.8.1, Theorem [Vosper] `theo_Vosper` condition (iii), lines 256–267, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Borja/borja4.tex>: "`A` and `B` are arithmetic progressions with the same common difference".
