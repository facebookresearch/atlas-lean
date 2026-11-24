# Stored energy of the capacitor and inductor branches

For `n_B` branches, sets `C` and `L` of capacitor and inductor branches, real values `C_e` and
`L_e` and real branch voltages `v` and currents `i`, the stored energy is

`E = ∑_{e ∈ C} C_e v_e² / 2 + ∑_{e ∈ L} L_e i_e² / 2`,

capacitor energy plus inductor energy, with no mutual inductance. In the physical reading the
capacitances and inductances are positive; the formula is defined for all real values.
