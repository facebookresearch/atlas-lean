---
article_id: af_ad8cfb688f5fc9d7d9139464
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.ArakelovDivisor.sectionSet_finite
---

# Section Set finite

Every section set of an Arakelov divisor is finite. Clearing denominators by a
nonzero element of `𝓞 K` lands in the ring of integers, and the ordinary-radius
archimedean bounds transfer to uniform bounds on all complex embeddings, so
`NumberField.Embeddings.finite_of_norm_le` applies.

## Depends on

- [Arakelov Divisor](arakelov-divisor.md)
- [Section Set](section-set.md)

## Proof depends on

- [Mem section Set](mem-section-set.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.ArakelovDivisor](../../../../../../../../sources/v2/MathlibExt.md)
