# Poisson mutation kernel on a Kingman genealogy with topology

For a natural number `n` and `θ ≥ 0`, this kernel describes infinite-sites mutation on a Kingman
genealogy with topology. A genealogy `(t, h)` consists of real epoch lengths
`t = (t_2, …, t_n)`, `t_k` being the time during which there are `k` lineages, and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of the `n` genes. The kernel sends `(t, h)` to the product measure

`⊗_b Po((θ / 2) ℓ_b(t))`

on the vectors `N = (N_b)_b` of natural numbers indexed by the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) `b = (k, j)` of the
genealogy (`2 ≤ k ≤ n`, `j < k`): the mutation counts `N_b` are independent and `N_b` is Poisson
with mean `(θ / 2) ℓ_b(t)`. Here `ℓ_b(t) = max(t_k, 0)` is the
[length](../poisson-mutation-on-the-kingman-genealogy/kingman-branch-length.md) of a branch of
epoch `k`: a negative epoch length gives length `0`, and the counts on the branches of that epoch
are then `0` almost surely. Every value of the kernel is a probability measure. The kernel does
not depend on `h`: it is the
[Kingman mutation kernel](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-kernel.md),
at rate `θ / 2` per lineage, applied to `t`.
