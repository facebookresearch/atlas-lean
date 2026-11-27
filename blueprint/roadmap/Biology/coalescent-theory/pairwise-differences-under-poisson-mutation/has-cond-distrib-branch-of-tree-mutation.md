# Each branch count is conditionally Poisson given the genealogy

Let `μ` be an s-finite measure on a measurable space `Ω`, let `n` be a natural number and
`θ ≥ 0`. Let `X` map `Ω` to genealogies `(t, h)`, made of real epoch lengths `t = (t_2, …, t_n)`
and a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`h` of `n` genes, and let `N` map `Ω` to vectors of natural numbers indexed by the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy.
Suppose that `N` has conditional law `κ` given `X` under `μ`, where `κ` is the
[mutation kernel with topology](kingman-tree-mutation-kernel.md): the pair `(X, N)` is
`μ`-almost everywhere measurable and its image measure is the composition `μ_X ⊗ κ`, with `μ_X`
the image of `μ` under `X`. Then for every branch `b = (k, j)` the single count `N_b` has
conditional law `(t, h) ↦ Po((θ / 2) max(t_k, 0))` given `X` under `μ`: given the genealogy, it
is Poisson with mean `θ / 2` times the length of `b`.
