# Completed Tensor Product repr tmul

Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E` and `F` be
independent normed inner-product spaces over `𝕜`. Let `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` be Hilbert bases with arbitrary independent index types.
For every `x : E`, `y : F`, `i : ι` and `j : κ`, coordinate `(i,j)` of the
completed pure tensor `x ⊗ y` under the product-basis lp-two representation is
`b.repr x i * c.repr y j`. The tensor completion has its actual inner-product norm.
