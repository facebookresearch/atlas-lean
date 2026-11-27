# A steady box reactor has the left-null weighted totals of its inflow

Let `S` be the real stoichiometric matrix of `n` species and `m` reactions, and consider a
well-mixed box reactor with flow `F > 0`, volume `V > 0`, inflow concentrations `c_i^in` and
reaction rates `r_j`. If the concentrations `c_i` are at steady state,
`(F / V) (c_i^in - c_i) + ∑_j S_ij r_j = 0` for every species `i`, then every left-null vector `l`
of `S` (`∑_i l_i S_ij = 0` for every reaction `j`) gives equal weighted totals:
`∑_i l_i c_i = ∑_i l_i c_i^in`.
