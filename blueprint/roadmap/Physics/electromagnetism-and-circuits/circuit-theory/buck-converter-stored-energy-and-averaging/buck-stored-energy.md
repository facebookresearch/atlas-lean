# Stored energy of the ideal buck converter

For real numbers `L` and `C`, functions `i, v : ℝ → ℝ` (inductor current and capacitor voltage) and
a time `t`, the stored energy is the
[network stored energy](../energy-balance-of-rlc-networks/stored-energy.md) of the four-branch
network (source, inductor, capacitor, resistor) with the single capacitor branch `2` of capacitance
`C` at voltage `v(t)` and the single inductor branch `1` of inductance `L` at current `i(t)`. It
[equals](buck-stored-energy-eq.md) `L i(t)² / 2 + C v(t)² / 2`.
