# The right adjoint action replaces wedge entries by right brackets

Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let S be
another R-Lie algebra and ι : S →ₗ⁅R⁆ L. For n : ℕ, s : S and v : Fin n → L,
rightDegreeAdjointAction n s (ιMulti v) = ∑ i : Fin n, ιMulti(Function.update v i ⁅v_i,ι(s)⁆).
Every summand has coefficient +1.
