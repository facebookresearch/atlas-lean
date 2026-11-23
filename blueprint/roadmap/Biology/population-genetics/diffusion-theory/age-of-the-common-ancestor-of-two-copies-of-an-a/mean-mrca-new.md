# Mean Mrca New

Patterson's `M₁(y)` (Equation 16, Theorem 6(2)): in the diffusion reading, the
expected age (in units of `2N` generations) of the MRCA of two copies of an allele
known to be new (nonancestral) and now at frequency `y`:

`M₁(y) = -4 + 2 log y + (2π² - 12 dilog y) / (3y) + 2 (log y) / (1 - y)`.

Meaningful for `y ∈ (0, 1)`. At `y = 1` the Lean value is `2π² / 3 - 4`: the last
term `2 log 1 / (1 - 1)` evaluates to `0` by totalized division, so the value at `1`
is an artifact, `2` more than the limit `2 (π² - 9) / 3` of
`tendsto_meanMrcaNew_one`. The identity `meanMrcaNew_eq_integral` derives this
formula from Theorem 4.
