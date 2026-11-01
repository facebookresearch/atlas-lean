---
article_id: af_9a4ad437cab807b6f13f8561
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.witt_multigraded_dimension_formula
---

# Witt multigraded dimension formula

Witt's multigraded dimension formula for free Lie algebras: the
multihomogeneous component of multidegree `(n_1, ..., n_r)` of the free Lie
algebra has dimension `M(n_1, ..., n_r)`. The component is imported from
`MathlibExt.Algebra.Lie.FreeLieMultihomogeneousComponent` and the value `M`
from `MathlibExt.Algebra.Lie.WittMultigradedValue`.

Proof: The Lyndon-word basis identifies the component with the Lyndon words of
the prescribed content, which are counted by Möbius inversion.

## Depends on

- [Free Lie Multihomogeneous Component](../free-lie-multihomogeneous-component/free-lie-multihomogeneous-component.md)
- [Witt Multigraded Value](../witt-multigraded-value.md)

## Proof depends on

- [Finrank free Lie Multihomogeneous Component](finrank-free-lie-multihomogeneous-compon.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Lie.WittMultigradedDimension](../../../../../sources/v2/MathlibExt.md)
- Pieter Moree, *Convoluted Convolved Fibonacci Numbers*, Journal of Integer Sequences 7 (2004), Article 04.2.2, Witt's formula paragraph, lines 621–628, <https://cs.uwaterloo.ca/journals/JIS/VOL7/Moree/moree12.tex>.
