# Total quartet support of a tree

Let `X` be a finite set of taxa. Let `f q ρ` be real numbers, one for each set `q` of taxa and
family `ρ` of subsets, for example estimated frequencies of the resolutions of each four-taxon set.
The total quartet support of an
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
`T` on `X` is `S_f(T) = ∑_q ∑_ρ f q ρ`, the sum over the [four-taxon subsets](quartets.md) `q` of
`X` and over the [resolutions](resolutions.md) `ρ` of `q` that `T` [induces](induces.md). As `T`
induces [exactly one](exists-unique-induces.md) resolution `T|q` of each four-taxon set,
`S_f(T) = ∑_q f q (T|q)`.
