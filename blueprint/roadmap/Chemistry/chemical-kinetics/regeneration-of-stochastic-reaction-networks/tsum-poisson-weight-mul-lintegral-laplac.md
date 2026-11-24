# The forward-equation transfer, in Laplace form

For a complex-balanced network whose
chain is non-explosive (drift bound `L V ≤ a V + b`, `∑_s x_s ≤ V(x)`), the product-form law
`π_c` is stationary for the chain in the Laplace sense: for every `a > 0` and `0 ≤ g ≤ 1`,
`∑_x π_c(x) E_x[∫_0^∞ a e^{-a t} g(X_t) dt] = ∑_x π_c(x) g(x)`. For `g` the indicator of a state
`y` this says that `t ↦ P_{π_c}(X_t = y)` has the Laplace transform of the constant `π_c(y)`;
the fixed-time identity `P_{π_c}(X_t = y) = π_c(y)` (the hypothesis `htransfer` of
`StochasticCRNErgodicity.ergodic_of_isComplexBalanced`) would follow by uniqueness of Laplace
transforms, which is not proved here.
