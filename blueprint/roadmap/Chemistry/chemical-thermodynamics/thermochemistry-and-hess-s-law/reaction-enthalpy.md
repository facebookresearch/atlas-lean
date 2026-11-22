# Reaction enthalpy as a linear functional

Reaction enthalpy as a linear functional on the reaction space: for a fixed assignment of
molar enthalpies `H : ι → ℝ`, the enthalpy of the reaction `ν` is `∑ i, ν i * H i`, with
products positive and reactants negative. `ΔH` is per mole of reaction as written: scaling the
written equation scales `ΔH` (see `hess_smul` and `hess_double`).
