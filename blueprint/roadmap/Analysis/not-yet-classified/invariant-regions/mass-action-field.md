# Mass Action Field

The mass-action vector field `F y i = ∑ j, N i j * (k j * ∏ s, y s ^ α j s)` of a reaction
network with species `ι` and reactions `J`: `N i j` is the net change of species `i` in reaction
`j`, `α j s` is the exponent of species `s` in the rate of reaction `j`, and `k j` is the rate
constant of reaction `j`.

For a network with reactant and product complexes `src` and `prod`, the choice
`N s j = prod j s - src j s`, `α = src` gives the field
`MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork.massActionField`, and this choice
always satisfies the compatibility condition of `massActionField_nonneg_of_eq_zero`.
