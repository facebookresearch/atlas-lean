# Radon–Nikodym derivative at an atom

If `μ` has a
Lebesgue decomposition with respect to `ν`, then at every point `x` with `ν {x} ≠ 0` and
`ν {x} ≠ ∞` the derivative is `μ.rnDeriv ν x = μ {x} / ν {x}`. The singular part of `μ`
vanishes at `x` because it is carried by a `ν`-null set, so `μ` is not assumed absolutely
continuous with respect to `ν`. The finiteness hypothesis `ν {x} ≠ ∞` cannot be dropped:
for `μ = ν = ∞ • Measure.dirac x`, `μ.rnDeriv ν x` is nonzero, while
`μ {x} / ν {x} = ∞ / ∞ = 0`.
