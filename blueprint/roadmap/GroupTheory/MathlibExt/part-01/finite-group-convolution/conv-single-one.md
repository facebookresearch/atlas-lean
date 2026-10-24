---
article_id: af_7af666e90747f8426a2bd5e8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv_single_one
---

# Conv single one

The delta function at the identity is a left identity for convolution.

Proof: Expand the convolution and collapse the sum at the unique nonzero value
of `Pi.single`, following the identity-element argument in Terras, Ch. 1.

## Depends on

- [Conv](conv.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.FiniteGroupConvolution](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 1 (identity of the group algebra).
