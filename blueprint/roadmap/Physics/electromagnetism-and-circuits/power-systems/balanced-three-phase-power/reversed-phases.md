# Balanced negative-sequence phase set

For a complex phasor `X`, the balanced negative-sequence (acb) phase set is the triple

`(X_a, X_b, X_c) = (X, α X, α² X) = (X, X e^{2πi/3}, X e^{-2πi/3})`,

indexed by the integers mod 3 (`0, 1, 2` for the phases `a, b, c`), where `α = e^{2πi/3}` is the
[rotation operator](../symmetrical-components-of-three-phase-systems/alpha.md). It is the
[positive-sequence set](balanced-phases.md) with phases `b` and `c` exchanged: with phasors
rotating as `e^{iωt}`, phase `c` lags phase `a` by `2π/3` and phase `b` lags phase `c` by `2π/3`,
so the phases follow the order `a, c, b`. For `X = 0` all three phasors are `0`.
