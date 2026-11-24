# Stagnation energy not isentropic

The energy balance alone does not give the isentrope: under the hypotheses of
`stagnation_temperature_ratio` with `M > 0`, and a static state `p = ρ R T` with `ρ > 0`, the
state with pressure `p0 = p`, density `ρ0 = p / (R T0)` and the same `T0` obeys the ideal-gas
law, but its pressure ratio `p0 / p = 1` is below the isentropic `(T0 / T) ^ (γ / (γ - 1))`
(its entropy rises by `cp log (T0 / T) > 0`).
