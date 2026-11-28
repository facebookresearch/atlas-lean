# Break Even

The **break-even concentration** `λ = a / (m / D - 1)`, meaningful when `m > D`. For `D ≠ 0`
the formula equals `steadyConc m a D = D a / (m - D)`, the substrate coordinate of the chemostat
model's candidate interior state `interiorState` (`breakEven_eq_steadyConc`). That candidate is
a steady state with positive biomass only for positive parameters with `D < m S⁰ / (a + S⁰)`,
that is `m > D` and `λ < S⁰` (`equilibria_and_washout_threshold`).
