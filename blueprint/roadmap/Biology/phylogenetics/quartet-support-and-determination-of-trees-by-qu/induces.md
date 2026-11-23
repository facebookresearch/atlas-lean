# Resolution of a taxon set induced by a tree

Let `X` be a finite set of taxa. An
[unrooted binary phylogenetic tree](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/unrooted-binary-tree.md)
`T` on `X` induces a family `ρ` of subsets of `X` on a set `q ⊆ X` if some
[edge split](../splits-compatibility-ultrametrics-and-upgma/edge-splits.md) `B` of `T` cuts `q` into
a member of `ρ`: `q ∩ B ∈ ρ`. For a resolution `ρ = {A, q \ A}` of a four-taxon set `q`, this says
that some edge of `T` separates `A` from `q \ A`, that is, the quartet tree `T|q` is `ρ`.
