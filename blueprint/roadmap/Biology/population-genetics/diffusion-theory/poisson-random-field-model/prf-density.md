# Sawyer–Hartl Poisson random field density

The Sawyer–Hartl (1992) Poisson-random-field density: the expected number of sites per unit
frequency at which the derived allele has frequency `x`, for scaled mutation rate `θ = 4Nu`
and scaled genic selection `σ = 2Ns`:
`θ · u_σ(1 - x) / (x (1 - x))` with `u_σ = kimuraFixation σ`, i.e.
`θ (1 - e^{-2σ(1 - x)}) / ((1 - e^{-2σ}) x (1 - x))`, and `θ / x` when `σ = 0`.
The model domain is `θ > 0` and `x ∈ (0, 1)`; at `x = 0, 1` Lean's `a / 0 = 0` gives the junk
value `0`.
