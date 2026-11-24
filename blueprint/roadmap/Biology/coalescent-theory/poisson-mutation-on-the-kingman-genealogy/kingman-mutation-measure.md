# The marked Kingman model

For a natural number `n` and `θ ≥ 0`, the marked Kingman model is the measure on pairs `(t, N)`
of real epoch-length vectors `t = (t_k)_{2 ≤ k ≤ n}` and natural-number branch-count vectors
`N = (N_b)` that draws `t` from the product of the exponential laws with rates `C(k, 2)`
([canonical probability space](../kingman-s-coalescent-and-watterson-s-estimator/pi-measure.md))
and then, given `t`, draws `N` from the [Kingman mutation kernel](kingman-mutation-kernel.md):
independent Poisson counts with means `(θ / 2) max(t_k, 0)` on the `k`
[branches](kingman-branch.md) of epoch `k`. It is a probability measure.
