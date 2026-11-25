# The Poisson mean of a branch is measurable in the genealogy

For every natural number `n`, every `θ ≥ 0` and every
[branch](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) `b = (k, j)` of a Kingman
genealogy of `n` genes (`2 ≤ k ≤ n`, `j < k`), the map

`(t, h) ↦ (θ / 2) ℓ_b(t) = (θ / 2) max(t_k, 0)`,

from genealogies (real epoch lengths `t = (t_2, …, t_n)` and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`)
to the nonnegative reals, is measurable for the Borel σ-algebra on the epoch lengths and the
σ-algebra of all sets of histories. It is the Poisson mean of the number of mutations on `b` under
the [mutation kernel with topology](kingman-tree-mutation-kernel.md); `ℓ_b(t)` is the
[length](../poisson-mutation-on-the-kingman-genealogy/kingman-branch-length.md) of `b`, which is
`0` when `t_k < 0`.
