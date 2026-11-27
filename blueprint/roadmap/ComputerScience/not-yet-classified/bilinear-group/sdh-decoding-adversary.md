# q-SDH decoding adversary

It ignores the power tuple and `g2`, decodes
`x` from the supplied `G2` element with `exp2.symm`, and outputs `(1 - x, g1)`
as a `PMF` via `PMF.pure`. In the toy model this reads `Multiplicative.toAdd`;
in any instance the same attack decodes with `exp.symm`, exhibiting the
insecurity of every instance against unrestricted adversaries. It works at
every `t`, including `t = 0`.
