# Exterior basis and PBW coordinates give finitely supported polynomial coefficients

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let I be a linearly
ordered index type, b : Module.Basis I R L and P = MvPolynomial I R. For n : ℕ,
envelopingCoefficientCoordinates gives an R-linear equivalence C_n ≃ₗ[R] (Set.powersetCard I n
→₀ P). It first swaps tensor factors, takes coefficients in the exterior basis b.exteriorPower
n, and applies the PBW polynomial coordinate map to each U-valued coefficient.
