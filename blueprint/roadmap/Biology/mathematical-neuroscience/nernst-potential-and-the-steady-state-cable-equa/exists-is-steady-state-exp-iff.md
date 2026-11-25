# A nonzero decaying exponential is a steady state iff its rate is 1/λ

Let `r_m > 0`, `r_i > 0`, `a > 0` and `c ≠ 0` be real numbers. The exponential voltage profile
`V(x) = c e^(-a x)` is the voltage of a [steady state](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) of the passive cable on the whole real line, that is,
there is an axial current `I` with `V' = -r_i I` and `I' = -V / r_m` at every `x ∈ ℝ`, if and only
if

`a = 1 / λ`, with `λ = √(r_m / r_i)` the [length constant](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/length-constant.md).

This derives the length constant from the core-conductor equations.
