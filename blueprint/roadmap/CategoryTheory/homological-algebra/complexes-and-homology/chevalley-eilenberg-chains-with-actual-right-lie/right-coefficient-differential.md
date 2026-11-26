# Tensor coordinates transport the left differential to right coefficient chains

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and M :
RightLieModuleCat.{w} R L a right Lie module with action m·x = M.action x m. Let M_left have
left action ⁅x,m⁆ = −m·x. For n : ℕ, δ_right,n = E_n⁻¹ ∘ coefficientDifferential_(M_left),n ∘
E_(n+1), where E_n is rightCoefficientDegreeEquiv. Its source is M ⊗ ⋀^(n+1)L and target M ⊗
⋀^nL.
