# Wall Pressure

Pressure on a wall in the elastic-wall model (CH08.3), defined as momentum transfer per unit
area per unit time: particle `i ∈ s` delivers momentum `Δp i` to the wall once every `τ i`, so
the wall receives momentum at the rate `∑ i ∈ s, Δp i / τ i`, spread over its area `A`. A
particle with `Δp i = 0` contributes `0` regardless of its `τ i`, so the definition never
needs an (unphysical) infinite flight time to be represented as `τ i = 0`. Neither
Mathlib nor ATLAS `main` defines a kinetic (momentum-flux) pressure; Physlib's
`NVEHamiltonian.pressure` (used by `IdealGas.ideal_gas_law`) is the thermodynamic pressure
`-∂A/∂V`, a different quantity.
