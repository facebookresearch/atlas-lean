# From the exterior algebra of the limit to the algebra limit

Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. The `R`-algebra
map `toDirectLimit : ExteriorAlgebra R L → C` sends `ι(x)` to `directLimitGenerator x` and
hence `ι(u_i x)` to `j_i(ι x)`.
