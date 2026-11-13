# Path-space measure of a Markov semigroup

The canonical path-space measure selected from Kolmogorov extension.

As for `finiteLaw`, no identity-at-zero hypothesis is built into this generic
object: its time-zero marginal is `K 0 x` unless the caller proves
`K 0 = Kernel.id`.
