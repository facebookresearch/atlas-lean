# Marked Kingman model with random-joining topology

For a natural number `n` and `θ ≥ 0`, the marked Kingman model with topology is the probability
measure on pairs `((t, h), N)` of a genealogy and mutation counts on its branches obtained by
composing the [Kingman genealogy law](kingman-genealogy-measure.md) with the
[mutation kernel with topology](kingman-tree-mutation-kernel.md). The genealogy `(t, h)` has
independent epoch lengths, `t_k` exponential with rate `C(k, 2)`, and an independent
random-joining [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h`; given `(t, h)`, the counts `N_b` on the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) `b = (k, j)` are
independent, `N_b` Poisson with mean `θ / 2` times the length `max(t_k, 0)` of `b`; since the
epoch lengths are almost surely positive, this Poisson mean is `(θ / 2) t_k` almost surely.
