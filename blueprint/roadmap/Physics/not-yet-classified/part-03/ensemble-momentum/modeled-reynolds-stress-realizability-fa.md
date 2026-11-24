# A positive eddy viscosity does not give realizability

For `k ≥ 0`, `νt > 0` and a
symmetric trace-free `S` the closure need not be positive semidefinite (`Matrix.PosSemidef`),
although the quadratic form of every Reynolds stress of `L²` velocities is nonnegative
(`reynoldsStress_posSemidef`): for the plane-strain fixture the quadratic form of the closure
along `e₀` is `Rm₀₀ = -4/3 < 0`.
