# Pairwise differences as mutations on the separating branches

Let `Ω` be a set and `n` a natural number. Let `H` map each `ω ∈ Ω` to a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)
`H(ω)` of `n` genes, and let `N` map each `ω` to natural numbers `N_ω(b)`, the numbers of
mutation events on the [branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md)
`b` of the genealogy. For a set `s` of genes of the sample, the number of differences of `s` is
the real number

`D_s(ω) = ∑_{b ∈ P_{H(ω)}(s)} N_ω(b)`,

where `P_h(s)` is the [set of branches](pair-path.md) of the history `h` ancestral to exactly one
gene of `s`. For a pair `s = {x, y}` these branches form the path between `x` and `y` through
their most recent common ancestor, and under infinite sites `D_s` is the number of sites at which
the two sequences differ.
