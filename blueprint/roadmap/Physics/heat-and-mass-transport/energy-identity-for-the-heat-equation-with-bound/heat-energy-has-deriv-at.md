# Heat Energy has Deriv At

Quadratic heat-energy identity with explicit boundary work, at
one time `t`: for a temperature field `u` with actual time
derivative `ut`, spatial derivatives `ux`, `uxx` in `HasDerivAt`
form on `Set.uIcc 0 L` (`0 ≤ L`), satisfying
`ut t x = D * uxx t x + src t x` there, the energy
`E(τ) = ∫₀ᴸ u(τ, x)^2 / 2 dx` has derivative at `t` equal to
`-D * ∫₀ᴸ ux^2 dx + D * (u(t, L) * ux(t, L) - u(t, 0) * ux(t, 0))
+ ∫₀ᴸ u * src dx`. The boundary terms are retained, not discarded.
All hypotheses are scoped to the single time `t` and the interval
`[0, L]`. The hypothesis `hE` is the differentiation under the
integral, as a `HasDerivAt` for the energy itself; `ut` is
required to be the actual time derivative (`hut`). No joint
regularity hypothesis is declared: the assumptions are exactly
the pointwise derivative and continuity data at this `t`. The integration by parts is proved
from the stated derivative and continuity data. The first term is
the diffusion contribution; it is a dissipation only when
`0 ≤ D` (see `diffusion_contribution_nonpos`).
