# Exponential stability of the principal eigenvector

**Exponential stability of the principal eigenvector** (Oja 1982). Under the hypotheses of
`tendsto_oja`, there are `δ > 0`, `K > 0` and `κ > 0` such that every solution `z` of the
averaged Oja ODE on `[0, ∞)` with `‖z(0) - c‖ < δ` satisfies
`‖z(t) - c‖ ≤ K e^{-κ t} ‖z(0) - c‖` for all `t ≥ 0`, and likewise every solution with
`‖z(0) + c‖ < δ` satisfies `‖z(t) + c‖ ≤ K e^{-κ t} ‖z(0) + c‖` for all `t ≥ 0`.

## Sources

- E. Oja, "A simplified neuron model as a principal component analyzer", J. Math. Biol. 15 (1982) 267–273.
