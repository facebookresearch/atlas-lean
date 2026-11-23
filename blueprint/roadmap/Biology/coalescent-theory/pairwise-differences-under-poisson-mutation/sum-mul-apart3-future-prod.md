# Two pairs sharing a gene, from three distinct lineages

Given anything determined by the
first `t` steps, the remaining coalescence times of `{a, b}` and `{a, c}` have product moment
`E[τ_{ab}^{(t)} τ_{ac}^{(t)}; a, b, c apart] = (4/3) P(a, b, c apart)`. While the three are
apart, the next event merges `b` with `c` (leaving one pair with `E[τ²] = 2`) with probability
`1 / C(k, 2)`, ends one of the pairs with probability `2 / C(k, 2)`, and otherwise keeps all
three apart.
