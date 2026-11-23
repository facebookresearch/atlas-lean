# Delta-method variance of a studentized statistic

For `v > 0`, every measure `μ` and all real functions `N` and `V` on the sample space, the
linearization `(√v)⁻¹ (N - 0) + 0 · (V - v) = N / √v` of `N / √V` at `(0, v)`, given by the
[derivative at a zero numerator](has-fderiv-at-div-sqrt-zero.md), has variance `Var(N) / v`
under `μ`. Here, for every measure, `Var(X) = ∫ (X - ∫ X dμ)² dμ`, with `∫ X dμ = 0` when `X` is
not integrable and `Var(X)` read as `0` when this integral is infinite; for a probability measure
and a square-integrable `X` it is the usual variance.
