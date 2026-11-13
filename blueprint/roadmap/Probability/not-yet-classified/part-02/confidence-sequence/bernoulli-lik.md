# Bernoulli Lik

Bernoulli likelihood: `p` at `x = 1`, `1 - p` at `x = 0`, and `0` otherwise. This is
the likelihood of Mathlib's Nat-valued Bernoulli law, which assigns no mass outside
`{0, 1}`; treating every non-`1` observation as a failure would be wrong off the support.
