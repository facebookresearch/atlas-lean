# The coefficient tensor comparisons form a natural isomorphism

Let `k : Type u`, `R : Type v` be commutative rings with `R` a `k`-algebra, and `M : Type w`
have compatible commuting `k`- and `R`-module actions and a right `R`-action satisfying `op(r)
• m=r • m`. Put `h=max(u,v,z)` and `h'=max(u,v,w,z)`. The comparisons `[m,n] ↦ m⊗n` form a
natural isomorphism from `Left.functor k R R M` to the functor `N ↦ M ⊗[R] N`, from
`ModuleCat.{h} R` to `ModuleCat.{h'} R`.
