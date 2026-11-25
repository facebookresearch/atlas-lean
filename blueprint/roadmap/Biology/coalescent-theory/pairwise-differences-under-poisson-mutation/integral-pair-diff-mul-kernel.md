# Product moment of two pairwise differences given the genealogy

Let `n` be a natural number, `θ ≥ 0` and `g = (t, h)` a genealogy: real epoch lengths
`t = (t_2, …, t_n)` and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of `n` genes. Under the [mutation kernel with topology](kingman-tree-mutation-kernel.md) at `g`,
written `κ_g`, the branch counts `N_b` are independent Poisson with means
`λ_b = (θ / 2) max(t_k, 0)` for `b = (k, j)`. For sets `s` and `s'` of genes, let `P_h(s)` be the
[set of branches](pair-path.md) of `h` ancestral to exactly one gene of `s`, and write
`Σ_s(x) = ∑_{b ∈ P_h(s)} x_b`. Then

`∫ Σ_s(N) Σ_{s'}(N) dκ_g(N) = Σ_s(λ) Σ_{s'}(λ) + ∑_{b ∈ P_h(s) ∩ P_h(s')} λ_b`.

When the counts have conditional law the kernel given the genealogy and `s`, `s'` are pairs, the
left side is the conditional mean of the product `D_s D_{s'}` of the
[numbers of differences](pair-diff.md) given the genealogy `g`, and the right side is the product
of the conditional means plus the Poisson variance `λ_b` of each branch separating both pairs.
