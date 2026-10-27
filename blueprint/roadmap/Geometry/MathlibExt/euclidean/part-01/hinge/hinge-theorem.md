---
article_id: af_955f04409dc9c052a90de788
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hinge_theorem
---

# Hinge theorem

Hinge theorem: two nondegenerate (noncollinear) triangles with two pairs of
equal sides (`AB = DE`, `AC = DF`); if the included angle at `A` exceeds the
included angle at `D` (compared via inner products), then the opposite side
`BC` exceeds `EF`.

Proof: Mathlib's vector law of cosines, `norm_sub_sq_real`, compares the squared opposite-side
lengths, following Euclid's *Elements*, Book I, Proposition 24.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Hinge theorem of inner lt](hinge-theorem-of-inner-lt.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Hinge](../../../../../../sources/v2/MathlibExt.md)
- Euclid's Elements, Book I, Proposition 24 (https://mathcs.clarku.edu/~djoyce/elements/bookI/propI24.html); see also https://en.wikipedia.org/wiki/Hinge_theorem.
