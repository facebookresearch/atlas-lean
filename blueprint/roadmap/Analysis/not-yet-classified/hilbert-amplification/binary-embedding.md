# Binary basis embedding from an index bijection

Let `𝕜` be real or complex, `H` a
normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`, and `e : (Fin
2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`. `binaryEmbedding
b e i : H →ₗᵢ[𝕜] H` is `U_i`, the embedding corresponding to the injection `j ↦ e(i,j)`.
