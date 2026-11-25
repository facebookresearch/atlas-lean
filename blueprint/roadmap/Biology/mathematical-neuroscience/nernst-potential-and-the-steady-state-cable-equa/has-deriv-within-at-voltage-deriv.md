# Steady states satisfy the steady-state cable equation λ² V'' = V

Let `r_m > 0` and `r_i > 0`, let `s` be a set of real positions, and let `V` and `I` be a [steady state](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) of
the passive cable on `s`: at every `x ∈ s`, `V` has derivative `-r_i I(x)` and `I` has derivative
`-V(x) / r_m` within `s`. Then at every `x ∈ s` the function `y ↦ -r_i I(y)`, which is the
derivative of `V` within `s`, has derivative `V(x) / λ²` within `s`, where `λ = √(r_m / r_i)` is
the [length constant](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/length-constant.md). Eliminating the axial current thus gives the steady-state cable equation `λ² V'' = V`,
with `V''` the derivative within `s` of `V' = -r_i I`.
