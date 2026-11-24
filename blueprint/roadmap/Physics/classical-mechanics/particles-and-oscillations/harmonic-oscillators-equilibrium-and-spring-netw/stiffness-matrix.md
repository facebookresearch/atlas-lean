# Stiffness Matrix

Stiffness matrix (DEF): diagonal `(∑ j, k i j) + w i`, off-diagonal
`-k i j`. For reciprocal weights without self-springs (`k i j = k j i`,
`k i i = 0`), row `i` is the force balance on node `i` and half the quadratic
form is `springEnergy` (`springEnergy_eq_quadForm`).
