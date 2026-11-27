# The homogeneous directed-limit comparison

Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For `n : ℕ`, the `R`-linear map
`directLimitComparison R M f n : C_n → Λ^n_R L` sends `v_i(x)` to `exteriorPower.map n u_i x`.
