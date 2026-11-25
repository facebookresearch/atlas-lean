# Delta-method variance of a studentized statistic

For `v > 0`, every measure `μ` and all real functions `N` and `V` on the sample space, the
linearization `(√v)⁻¹ (N - 0) + 0 · (V - v) = N / √v` of `N / √V` at `(0, v)`, given by the
[derivative at a zero numerator](has-fderiv-at-div-sqrt-zero.md), has variance `Var(N) / v`
under `μ`; no measurability of `N` or `V` is needed. Here `Var(X)` is the lower (extended)
integral `∫⁻ |X - m|² dμ` of the squared distance to `m = ∫ X dμ`, taken as a real number: the
value `∞` is read as `0`, and `m = 0` when `X` is not integrable. For an almost everywhere
measurable `X` this equals the ordinary integral `∫ (X - m)² dμ` (both are `0` when the lower
integral is infinite); without measurability the two can differ. For a probability measure and a
square-integrable `X` it is the usual variance.
