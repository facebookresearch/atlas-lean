# Positive finite Cuntz family by successive last-leaf splitting

Let `𝕜` be real or
complex, `H` a normed inner-product `𝕜`-space with Hilbert basis `b : HilbertBasis ι 𝕜 H`,
and `e : (Fin 2 × ι) ≃ ι` an index bijection. Put `U_i b_j=b_(e(i,j))` for `i : Fin 2`.
For `N : ℕ+`, form `S_N` from the singleton family `[I]` by repeatedly replacing its last
operator `V` with `V U_0,V U_1` until the family has `N` operators. `finiteFamily b e N :
Fin N → B(H)` is this family `S_N`, with the unchanged earlier operators followed by `V
U_0,V U_1` at each split.
