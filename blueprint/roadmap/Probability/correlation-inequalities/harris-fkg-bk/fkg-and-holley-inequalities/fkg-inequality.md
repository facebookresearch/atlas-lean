# FKG inequality

The **FKG inequality** (Fortuin, Kasteleyn, Ginibre 1971). Let `π` be a probability weight on
`ConfigSpace E` (`π ≥ 0`, `∑ π = 1`) satisfying the FKG lattice condition. Then any two monotone
functions `f g : ConfigSpace E → ℝ` are positively correlated:
`E_π[f] * E_π[g] ≤ E_π[f * g]`.

See also Mathlib's `fkg`, which assumes `f, g ≥ 0` and does not normalize `π`; this version
removes the sign condition by shifting `f` and `g` by their values at `⊥`.
