# The right boundary is bracket differential plus signed right actions

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and M :
RightLieModuleCat.{w} R L a right Lie module with action m·x = M.action x m. Let M_left have
left action ⁅x,m⁆ = −m·x. For xs : Fin(n+1) → L, δ_right,n(m ⊗ ιMulti xs) = m ⊗
differential_CE,n(ιMulti xs) + ∑ i : Fin(n+1), (−1 : R)^i.val • ((m·xs_i) ⊗ ιMulti(xs ∘
i.succAbove)).
