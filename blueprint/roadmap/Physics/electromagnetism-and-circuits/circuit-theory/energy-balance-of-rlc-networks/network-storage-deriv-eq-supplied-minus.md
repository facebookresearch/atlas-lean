# Energy balance: stored-energy rate is supplied power minus losses

Let `B` be a real matrix with `n_N` rows and `n_B` columns, and let `R`, `L`, `C` and `S` be a
[branch partition](is-branch-partition.md) with resistances `R_e ≥ 0` on `R`, inductances
`L_e > 0` on `L` and capacitances `C_e > 0` on `C`. Let `φ` and `j` be node potentials and node
injections and `v` and `i` branch voltages and currents, all depending on time, and let `t` be a
time at which

- `v(t) = Bᵀ φ(t)` and `B i(t) = j(t)`;
- `v_e(t) = R_e i_e(t)` for `e ∈ R`, `i_e(t) = C_e v_e'(t)` for `e ∈ C` and
  `v_e(t) = L_e i_e'(t)` for `e ∈ L`;
- the capacitor voltages and the inductor currents are differentiable at `t`.

Then the derivative at `t` of the [stored energy](stored-energy.md) `E` is

`E'(t) = φ(t) · j(t) − P_S(t) − P_R(t)`,

the supplied node power minus the [power absorbed by the sources](source-absorbed-power.md)
`P_S = ∑_{e ∈ S} v_e i_e` and the [resistive loss](resistive-loss.md) `P_R = ∑_{e ∈ R} R_e i_e²`.
