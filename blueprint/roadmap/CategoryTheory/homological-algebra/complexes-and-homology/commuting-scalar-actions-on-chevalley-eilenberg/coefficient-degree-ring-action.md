# The commuting action gives R-linear endomorphisms of each CE degree

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. For
n : ℕ, coefficientDegreeRingAction is the ring homomorphism S → Module.End R
((coefficientComplex R L X).X n) obtained by evaluating the chain action in degree n.
