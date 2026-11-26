# The right boundary has the explicit bracket-boundary and action presentation

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and M :
RightLieModuleCat.{w} R L a right Lie module with action m·x = M.action x m. Let M_left have
left action ⁅x,m⁆ = −m·x. For xs : Fin(n+1) → L, δ_right,n(m ⊗ ιMulti xs) = m ⊗
bracketBoundary R L n xs + ∑ i, (−1 : R)^i.val • ((m·xs_i) ⊗ ιMulti(xs ∘ i.succAbove)).
