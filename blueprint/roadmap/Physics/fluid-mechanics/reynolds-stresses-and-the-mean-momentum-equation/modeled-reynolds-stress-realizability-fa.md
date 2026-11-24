# A positive eddy viscosity does not make the closure semidefinite

It is not true that for all real `k ≥ 0`, `νt > 0` and every symmetric real `3 × 3` matrix `S` with
trace `0` the [closure](modeled-reynolds-stress.md) `Rm = (2 k / 3) I - 2 νt S` is positive
semidefinite: for the [plane-strain fixture](modeled-reynolds-stress-plane-strain.md) its quadratic
form along `e₀` is `Rm₀₀ = -4/3 < 0`. The quadratic form of every
[Reynolds stress of square-integrable velocities](reynolds-stress-pos-semidef.md) is nonnegative, so
the closure need not be realizable even when it extracts energy from the mean flow.
