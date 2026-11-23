# Kinetic pressure on a wall

Pressure on a wall in the elastic-wall model, defined as momentum transfer per unit area per unit
time: particle `i ∈ s` delivers momentum `Δp i` to the wall once every `τ i`, so the wall receives
momentum at the rate `∑ i ∈ s, Δp i / τ i`, spread over its area `A`. A particle with `Δp i = 0`
contributes `0` regardless of its `τ i`, so the definition never needs an (unphysical) infinite
flight time to be represented as `τ i = 0`. It is defined for all real `τ i` and `A`: by the
convention `x / 0 = 0`, a particle with `τ i = 0` contributes `0`, and the pressure is `0` for
`A = 0`. The intended domain is `A > 0`, with `τ i > 0` for every particle with `Δp i ≠ 0`. It is
a kinetic (momentum-flux) pressure, a different quantity from the thermodynamic pressure
`-∂F/∂V`, with `F` the Helmholtz free energy.
