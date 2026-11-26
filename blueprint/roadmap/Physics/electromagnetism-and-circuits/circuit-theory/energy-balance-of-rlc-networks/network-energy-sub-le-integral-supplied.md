# The stored-energy increase is at most the supplied energy

Let `B` be a real `n_N × n_B` matrix and `R`, `L`, `C`, `S` a
[branch partition](is-branch-partition.md) of the branches, with real values `R_e ≥ 0` on `R`,
`L_e > 0` on `L` and `C_e > 0` on `C` (as in the
[energy balance](network-storage-deriv-eq-supplied-minus.md)). Let `φ`, `j`, `v` and `i` depend on
time and let `a ≤ b`. Suppose that at every `s ∈ [a, b]` the laws `v(s) = Bᵀ φ(s)`, `B i(s) = j(s)`,
`v_e(s) = R_e i_e(s)` on `R`, `i_e(s) = C_e v_e'(s)` on `C` and `v_e(s) = L_e i_e'(s)` on `L` hold,
with the capacitor voltages and inductor currents differentiable at `s`. Suppose also that the net
supplied power `p(s) = φ(s) · j(s) − P_S(s)` is continuous on `[a, b]` and that `p − P_R` is
integrable on `[a, b]`, with `P_S` the [source power](source-absorbed-power.md) and `P_R` the
[resistive loss](resistive-loss.md). Then the [stored energy](stored-energy.md) satisfies

`E(b) − E(a) ≤ ∫ from a to b of p(s) ds`.

The resistive loss is nonnegative because the resistances are.
