# The exact right homology carrier computes lifted enveloping Tor

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and A :
RightLieModuleCat.{w} R L. Put M = toLeft A, with ⁅x,m⁆ = −A.action x m, and H = max u v v' w
w' z. Assume Module.Free R L. For n : ℕ, the tensor-flip homology comparison followed by
rawCoefficientHomologyEquivTorAt M gives H_n(CE_right(L,A)) ≃ₗ[R] rawRightLieCoefficientTorAt
A n.
