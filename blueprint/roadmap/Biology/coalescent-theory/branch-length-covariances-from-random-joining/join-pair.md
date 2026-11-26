# Expectation of a product at two steps of random joining

For natural numbers `a` and `b`, real functions `g` and `h` on lists of natural numbers and a
list `x` of natural numbers, let

`P_{a,b}(g, h)(x) = J^a(y ↦ g(y) · (J^{b - a} h)(y))(x)`,

where `J` is the
[transition operator of random joining](../expected-site-frequency-spectrum/join-step.md) and
`J^m` is its `m`-th iterate. For `a ≤ b` it is the expectation of `g` at step `a` times `h` at
step `b` of random joining started from `x`
([two-level Markov property](exists-finset-random-joining-pair.md)). For `b < a` the
natural-number subtraction `b - a` is `0`, and the value is `J^a(g h)(x)`.
