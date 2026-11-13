# Shannon Entropy Nats

Shannon entropy (nats) of a probability mass function on a finite type,
`∑ a, -(p a) * log (p a)`, with the `0 log 0 = 0` convention read off from
`Real.negMulLog` at the support: terms with `p a = 0` contribute `0`.
