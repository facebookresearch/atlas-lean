---
article_id: af_1c72fbb28850da65253ed718
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.charPair_conv
---

# Char Pair conv

Convolution theorem, coefficient form: pairing a convolution against a
one-dimensional character splits as a product of pairings.

Proof: Swap the finite sums, reindex by `x = y * z`, and use `map_mul` to
factor the character pairing, following Terras, Ch. 2–3.

## Depends on

- [Conv](conv.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.FiniteGroupConvolution](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2–3 (the Fourier transform takes convolution to pointwise products).
