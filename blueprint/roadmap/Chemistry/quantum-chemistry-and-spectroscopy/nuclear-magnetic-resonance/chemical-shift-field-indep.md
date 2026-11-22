# Chemical Shift field indep

Field independence to first order inside the shielding model: if
`ν = γ * B0 * (1 - σ) / (2 * Real.pi)` and
`νref = γ * B0 * (1 - σref) / (2 * Real.pi)`, then the shift equals
`1e6 * (σref - σ) / (1 - σref)`, which contains no `γ` and no `B0`.
Field-independence holds to first order inside this shielding model; it is not
a claim about higher-order (e.g. susceptibility) field dependence.
