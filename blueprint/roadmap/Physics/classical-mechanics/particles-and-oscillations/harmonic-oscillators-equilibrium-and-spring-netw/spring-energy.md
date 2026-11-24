# Spring Energy

Spring-network energy (DEF) for scalar displacements on a finite node
type: pair weights `k i j` plus wall springs of stiffness `w i` from node `i`
to a fixed wall. `w = 0` is the free network; `w i > 0` is a fixed end. The
definition accepts any `k`, but it is the physical spring energy only for
reciprocal weights `k i j = k j i` (as in `springEnergy_eq_quadForm`): the
ordered double sum then counts each spring twice, so the `1 / 4` gives each
spring its energy `(1 / 2) * k i j * (u j - u i) ^ 2`, and diagonal terms
vanish. For other `k` the pair `{i, j}` gets the average weight
`(k i j + k j i) / 2`.
