# Conditional binomial law in the fixed-total model, as a law

Under the hypotheses of
`cond_measureReal_counts_eq_binomial`, given `Cₐ + C_b = d` (an event of positive probability)
the count `Cₐ` has law `Bin(d, pₐ / (pₐ + p_b))`. For `pₐ = p_b` (McNemar's null of marginal
homogeneity, or the TDT null of no transmission distortion) with `pₐ > 0` this is
`Bin(d, 1/2)` after rewriting the success probability; if `pₐ = p_b = 0` the conditioning forces
`d = 0` and the stated law is `Bin(0, 0)`, equal to `Bin(0, 1/2)` as a measure but not
syntactically. The nonnegativity `hp₀` is needed only to form the success probability in
`[0, 1]`.
