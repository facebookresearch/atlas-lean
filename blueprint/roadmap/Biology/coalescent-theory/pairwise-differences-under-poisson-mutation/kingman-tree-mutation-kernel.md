# Poisson mutation kernel on a Kingman genealogy with topology

For a natural number `n` and `θ ≥ 0`, this kernel describes infinite-sites mutation on a Kingman
genealogy with topology. It goes from genealogies `(t, h)`, made of real epoch lengths
`t = (t_2, …, t_n)` (`t_k` being the time during which there are `k` lineages) and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of the `n` genes, to vectors `N = (N_b)_b` of natural numbers indexed by the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) `b = (k, j)` of the
genealogy (`2 ≤ k ≤ n`, `j < k`). It is defined as the pullback of the
[Kingman mutation kernel](../poisson-mutation-on-the-kingman-genealogy/kingman-mutation-kernel.md)
at rate `θ / 2` per lineage, which acts on epoch lengths alone, along the projection
`(t, h) ↦ t`: its value at `(t, h)` is the value of that kernel at `t`. So it does not depend on
the history `h`, and every value is a probability measure.

Evaluating it at a genealogy gives a
[product of Poisson laws](kingman-tree-mutation-kernel-apply.md): given `(t, h)`, the counts
`N_b` are independent and Poisson with mean `θ / 2` times the
[length](../poisson-mutation-on-the-kingman-genealogy/kingman-branch-length.md) `max(t_k, 0)` of
a branch of epoch `k`, so the counts on the branches of an epoch of negative length are `0` almost
surely.
