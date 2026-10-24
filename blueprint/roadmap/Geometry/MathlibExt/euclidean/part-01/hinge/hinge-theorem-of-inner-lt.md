---
article_id: af_838bbf45838b7332848fd685
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hinge_theorem_of_inner_lt
---

# Hinge theorem of inner lt

Hinge theorem for a real inner product space: if two pairs of adjacent sides have equal
lengths and the first included inner product is smaller, then its opposite side is longer.

Proof: Apply the law of cosines via `norm_sub_sq_real` and compare the squared side lengths.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Hinge](../../../../../../sources/v2/MathlibExt.md)
- Euclid's *Elements*, Book I, Proposition 24.
