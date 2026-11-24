# The stored energy changes at the capacitor and inductor power

Let `C` and `L` be sets of capacitor and inductor branches with real values `C_e` and `L_e`, let
`v` and `i` be branch voltages and currents depending on time, and let `t` be a time. Suppose that
the voltage `v_e` of every capacitor branch and the current `i_e` of every inductor branch are
differentiable at `t`, and that the branch laws hold at `t`:

`i_e(t) = C_e v_e'(t)` for `e ∈ C` and `v_e(t) = L_e i_e'(t)` for `e ∈ L`.

Then the [stored energy](stored-energy.md) `s ↦ E(v(s), i(s))` has at `t` the derivative

`∑_{e ∈ C} v_e(t) i_e(t) + ∑_{e ∈ L} v_e(t) i_e(t)`,

the power absorbed by the capacitor and inductor branches. No sign condition on `C_e` or `L_e` is
needed.
