# The mutation kernel at a genealogy is a product of Poisson laws

For every natural number `n`, every `θ ≥ 0` and every genealogy `g = (t, h)`, made of real epoch
lengths `t = (t_2, …, t_n)` and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of `n` genes, the value at `g` of the
[mutation kernel with topology](kingman-tree-mutation-kernel.md), the Kingman mutation kernel
pulled back along `(t, h) ↦ t`, is the product measure

`⊗_b Po((θ / 2) ℓ_b(t))`

over the [branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) `b = (k, j)`,
where `ℓ_b(t) = max(t_k, 0)` is the length of a branch of epoch `k`. Under this measure the
counts are independent and Poisson with means `(θ / 2) max(t_k, 0)`; the value does not depend
on `h`.
