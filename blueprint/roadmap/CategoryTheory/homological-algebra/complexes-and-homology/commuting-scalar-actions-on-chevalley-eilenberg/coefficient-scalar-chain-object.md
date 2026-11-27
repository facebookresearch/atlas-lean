# A CE degree carries the commuting coefficient-ring module structure

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
n : ℕ, coefficientScalarChainObject is the carrier of ⋀[R]^n L ⊗[R] X equipped with the
S-module action induced by coefficientDegreeRingAction. It is an object of ModuleCat.{max u v
w} S.
