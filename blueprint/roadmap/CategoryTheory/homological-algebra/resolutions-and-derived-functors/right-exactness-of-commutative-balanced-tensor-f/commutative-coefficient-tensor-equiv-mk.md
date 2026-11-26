# The commutative tensor comparison preserves a pure pair

Let `k : Type u`, `R : Type v` be commutative rings with `R` a `k`-algebra, and `M : Type w`
have compatible commuting `k`- and `R`-module actions and a right `R`-action satisfying `op(r)
• m=r • m`. Put `h=max(u,v,z)` and `h'=max(u,v,w,z)`. For `N : ModuleCat.{h} R`, `m : M`, and
`n : N`, `commutativeCoefficientTensorEquiv k R M hOp N ([m,n]) = m ⊗[R] n`, where `N` has its
ground action restricted along `k→R`.
