# Relabelling the interior nodes leaves the Schur complement unchanged

Let `m`, `p` and `q` be finite index sets, `e : q → p` a bijection, and `A`, `B` and `D` real
matrices of sizes `m × m`, `m × p` and `p × p`. With `B'(i, k) = B(i, e(k))` and
`D'(k, l) = D(e(k), e(l))`, the Schur complements agree: `A - B' D'⁻¹ B'ᵀ = A - B D⁻¹ Bᵀ`. Here the
matrix inverse is taken to be `0` for a singular matrix, and the identity holds for every `D`.
