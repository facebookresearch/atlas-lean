# Nodal conductance is the weighted Laplacian of the resistor arcs

Let `n_N` nodes and `n_B` branches be numbered, each branch `e` with a tail node `tail(e)` and a
head node `head(e)`, and let `R` be a set of resistor branches with real resistances `R_e`. The
[nodal conductance matrix](nodal-conductance.md) `G = B_R diag(R_e⁻¹) B_Rᵀ`, built from the resistor
columns `B_R` of the tail-positive [physical incidence](physical-incidence.md), equals the weighted
Laplacian of the resistor arcs,

`G = N diag(R_e⁻¹) Nᵀ`,

where `N` is the head-positive signed incidence of the resistor branches, with entries
`[head(e) = n] − [tail(e) = n]`. The two sign changes cancel. With the convention `0⁻¹ = 0`, a
branch of zero resistance contributes nothing on both sides.
