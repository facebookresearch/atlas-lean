# Unnormalized Dirichlet kernel

The unnormalized Dirichlet kernel `∏ θ a ^ (conc a - 1)`. For strictly positive
concentrations it is the Dirichlet density in the interior of the simplex up to its normalizing
constant (which does not depend on `θ` and so does not affect maximizers). For concentrations at
least `1`, the case of the MAP estimate, it also has the intended boundary values; concentrations in
`(0, 1)` have boundary singularities that `Real.rpow` does not represent, and no density
interpretation is claimed for nonpositive concentrations.
