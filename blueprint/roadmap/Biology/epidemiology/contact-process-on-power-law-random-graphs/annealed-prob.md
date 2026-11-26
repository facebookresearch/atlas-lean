# Annealed Prob

The probability, over the random graph and the contact process together, that at time `t`
the contact process started from all `n` vertices infected has at least `q n` infected vertices.
When the total weight `∑ H, nswWeight p H` is `0` (for a degree law `p`, when no simple graph on
`Fin n` has all its degrees in the support of `p`), Lean's `x / 0 = 0` convention makes
`nswLaw p n` identically `0`, and then the value is `0` for every `t` and `q`. (`hQ` records that
each contact-process rate matrix is a rate matrix.)
