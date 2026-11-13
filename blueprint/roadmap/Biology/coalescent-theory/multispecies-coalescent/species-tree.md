# Rooted binary species tree with branch lengths

A rooted binary **species tree** on the species `Fin n` with branch lengths: `leaf i` is
species `i`, and `node l r t` is the ancestral species of the species below `l` and `r`, where
`t` is the length, in coalescent units (`2N` generations), of the branch above the node, i.e.
the time during which the ancestral population of `l` and `r` exists before it merges with a
sister population. The length stored at the root node is not used: the root population lasts
until all lineages have coalesced. Leaf branch lengths are not recorded, because one gene
lineage is sampled per species and a single lineage cannot coalesce. A species tree on the
species `Fin n` labels each species by exactly one leaf; the type does not enforce this, and
the theorems below are about concrete trees with this property. The type accepts any real
branch length; the probabilistic statements assume nonnegative lengths (`NonnegLengths`).
