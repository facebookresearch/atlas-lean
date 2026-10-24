---
article_id: af_8d8100399ab46f8f96ebc4df
declaration: def
origin: cited
statement: formalized
lean: CoxeterMatrix.artinRelation
---

# Artin Relation

The Artin (braid) relation for the ordered pair `(i, j)`: the two alternating words of length
`M i j` in the generators `i` and `j` agree. It is encoded in the free group as
`⟨s i · s j · ⋯⟩ · ⟨s j · s i · ⋯⟩⁻¹`, which lies in the relation set exactly when both words are
declared equal.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Alternating Word](alternating-word.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.ArtinGroup](../../../../../sources/v2/MathlibExt.md)
