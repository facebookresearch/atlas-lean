# A lifted right chain term is the lifted coefficient-first tensor

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and M :
RightLieModuleCat.{w} R L a right Lie module with action m·x = M.action x m. Let M_left have
left action ⁅x,m⁆ = −m·x. For n : ℕ, (rightCoefficientComplexULift).X n = ModuleCat.of R
(ULift.{z} (M ⊗[R] Λ^nL)).
