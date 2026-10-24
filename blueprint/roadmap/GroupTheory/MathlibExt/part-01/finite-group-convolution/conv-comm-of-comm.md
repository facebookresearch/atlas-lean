---
article_id: af_5c877ddf7dca7d8112352532
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv_comm_of_comm
---

# Conv comm of comm

Convolution is commutative on abelian groups.

Proof: Reindex by `y ↦ y⁻¹ * x` and use commutativity in the group and in `ℂ`,
as in the commutative group-algebra argument in Terras, Ch. 2.

## Depends on

- [Conv](conv.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.FiniteGroupConvolution](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2 (commutative group algebra of an abelian group).
