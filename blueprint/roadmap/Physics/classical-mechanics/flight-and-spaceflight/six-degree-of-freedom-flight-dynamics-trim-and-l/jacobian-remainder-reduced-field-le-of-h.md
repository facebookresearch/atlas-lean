# The component-Hessian remainder theorem, instantiated

For `0 < r` and a deviation `δ`
with every coordinate at most `r` in absolute value, the reused componentwise bound
`Statistics.UncertaintyPropagation.jacobianRemainder_component_le_of_hessian`, applied on that box
with the Hessian bounds above, gives `|jacobianRemainder reducedField 0 δ i| ≤ H i / 2 * ‖δ‖²` in
the sup norm, `H = (6 r, 0, 0, r)`: the constants `3 r` and `r / 2` of components `0` and `3` are
three times those of `longitudinalRemainder_bounds`.
