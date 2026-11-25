# Completed Tensor Product apply

Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E` and `F` be
independent normed inner-product spaces over `𝕜`. Let `b : HilbertBasis ι 𝕜 E` and
`c : HilbertBasis κ 𝕜 F` be Hilbert bases with arbitrary independent index types.
For every `i : ι` and `j : κ`, the product basis vector at `(i,j)` is exactly
the completed pure tensor of `b i` and `c j` in `Completion (E ⊗[𝕜] F)`,
with its actual tensor inner-product norm.
