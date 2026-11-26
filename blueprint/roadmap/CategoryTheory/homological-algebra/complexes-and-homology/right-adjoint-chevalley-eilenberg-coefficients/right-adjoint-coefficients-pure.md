# The right adjoint action replaces each exterior entry by its right bracket

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let S be an R-Lie algebra, ι : S →ₗ⁅R⁆ L, n : ℕ, s : S and v : Fin n → L. The right
action of s on exteriorPower.ιMulti R n v equals ∑ i : Fin n, exteriorPower.ιMulti R n
(Function.update v i ⁅v_i, ι(s)⁆). The other entries retain their order, and every summand has
coefficient +1.
