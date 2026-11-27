# For r_i ≠ 0, zero axial current exactly where the voltage slope is 0

Let `r_m` and `r_i` be real numbers with `r_i ≠ 0`, let `s` be a set of real positions, and let `V`
and `I` be a [steady state](../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-steady-state.md) of the passive cable on `s`: at every `x ∈ s`, `V` has derivative `-r_i I(x)`
and `I` has derivative `-V(x) / r_m` within `s`. Let `x ∈ s` be a point at which derivatives within
`s` are unique (for example an interior point of `s`, or an endpoint of a nondegenerate interval
contained in `s`). Then the axial current vanishes at `x` exactly when the derivative of `V` within
`s` at `x` vanishes:

`I(x) = 0 ⟺ V'(x) = 0`.

So a sealed end, through which no axial current flows, is the zero-slope boundary condition for
the voltage.
