# A finite tuple has one common module stage

Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For `n : ℕ` and `a : Fin n → L`, there exist `i
: I` and `b : Fin n → M_i` with `u_i(b j)=a j` for every `j : Fin n`.
