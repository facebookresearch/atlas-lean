# LP dual vector of a dispatch dual witness

For rational nodal prices `λ`, a reference multiplier `ρ` and bound multipliers `μ_hi`, `μ_lo`
(generators) and `η_hi`, `η_lo` (branches), the dual vector, in the row order of the linear program,
is `(max(λ, 0), max(-λ, 0), max(ρ, 0), max(-ρ, 0), μ_hi, μ_lo, η_hi, η_lo)`. The free prices and
reference multiplier are split into positive and negative parts over the two rows of each equality;
the bound multipliers are passed unchanged. The vector passes the dual tests of the checker
[exactly when the witness is dual feasible](dual-vector-feasible-iff.md).
