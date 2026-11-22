# Butterfly Price nonneg

A nonnegative butterfly payoff has nonnegative price under positive state
pricing: with strictly positive state prices `psi`, the state-price-weighted
sum of butterfly payoffs is nonnegative. This is `Finset.sum_nonneg` plus
`mul_nonneg` applied to `butterflyPayoff_nonneg`; do not reprove either.
