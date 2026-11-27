# The balanced coefficient tensor is the ordinary R-tensor

Let `k : Type u`, `R : Type v` be commutative rings with `R` a `k`-algebra, and `M : Type w`
have compatible commuting `k`- and `R`-module actions and a right `R`-action satisfying `op(r)
• m=r • m`. Put `h=max(u,v,z)` and `h'=max(u,v,w,z)`. For `N : ModuleCat.{h} R`, the
outer-left balanced module `Left.obj k R R M N` is `R`-linearly equivalent to `M ⊗[R] N`, with
`[m,n] ↦ m⊗n`; both carriers lie in the category of size `h'`.
