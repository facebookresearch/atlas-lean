# Kinetic-theory pressure law for an isotropic gas

Elastic-wall pressure law: `p * V = (1 / 3) * N * m * ⟨v²⟩`.

Model hypotheses: the gas is a finite ensemble `s` of `N` particles of mass `m` in a cube of side
`L > 0` and volume `V = L ^ 3`, with wall area `L ^ 2`; particle `i` has velocity components `vx i`,
`vy i`, `vz i`; a collision with the wall perpendicular to `x` reverses the `x`-momentum and
transfers `Δp i = 2 * m * |vx i|`; a particle with `vx i ≠ 0` returns to that wall after the
round-trip time `τ i = 2 * L / |vx i|`; and isotropy `⟨vx²⟩ = ⟨vy²⟩ = ⟨vz²⟩ = (1 / 3) * v2` holds
for the mean `⟨·⟩` over the particles of `s`, where `v2` is the [mean square
speed](expect-speed-sq-of-isotropy.md). `V > 0` follows from `0 < L`. The identity holds for all `N`
and `m`; `0 < N` and `0 < m` record the physical domain. The flight-time equation is required only
for `vx i ≠ 0`: a particle with `vx i = 0` never reaches the wall, has `Δp i = 0`, and contributes
`0` regardless of its `τ i`, so no infinite flight time is represented as `τ i = 0`.
