# Commuting coefficient scalars give a CE chain complex over their ring

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. Let X be a Lie module over L with carrier universe w, let S be a ring, and let ρ :
S →+* Module.End R X satisfy ρ(s)(⁅l, m⁆) = ⁅l, ρ(s)(m)⁆ for every s : S, l : L and m : X. The
coefficientScalarChainObject degrees and coefficientScalarDifferential boundaries define a
chain complex in ModuleCat.{max u v w} S indexed by ℕ. Its underlying carriers and boundary
functions are those of the R-linear CE coefficient complex.
