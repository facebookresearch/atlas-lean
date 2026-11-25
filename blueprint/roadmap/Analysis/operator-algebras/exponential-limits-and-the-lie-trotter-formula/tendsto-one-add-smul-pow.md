# Compound-interest limit for the exponential in a Banach algebra

If `ε N → 0` with `ε N > 0` eventually,
`Y N → X` and `m N * ε N → t`, then `(1 + ε N • Y N) ^ m N → exp (t • X)`. This is
`NormedSpace.tendsto_one_add_inv_smul_pow` with the time scale `1 / M` replaced by an arbitrary
vanishing scale (for a Cannings model, the pair-coalescence probability `c_N`).
