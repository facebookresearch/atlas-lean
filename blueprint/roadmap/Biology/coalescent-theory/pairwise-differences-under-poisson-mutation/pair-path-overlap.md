# Overlap length of the paths of two pairs of genes

For a natural number `n`, a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of `n` genes, sets `s` and `s'` of genes of the sample and real epoch lengths
`t = (t_2, …, t_n)`, the overlap length is

`ℓ(P_h(s) ∩ P_h(s'))(t) = ∑_{b ∈ P_h(s) ∩ P_h(s')} ℓ_b(t)`,

the total length of the branches lying in both [paths](pair-path.md) `P_h(s)` and `P_h(s')`,
where `P_h(s)` is the set of branches ancestral to exactly one gene of `s`, and a branch
`b = (k, j)` has [length](../poisson-mutation-on-the-kingman-genealogy/kingman-branch-length.md)
`ℓ_b(t) = max(t_k, 0)`: a negative epoch length counts as `0`. For pairs `s` and `s'` these are
the branches separating both pairs, and a mutation there is counted in both numbers of
differences `D_s` and `D_{s'}`.
