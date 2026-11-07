# Neighbor joining recovers a tree within a radius

Neighbor joining **recovers the tree within radius `r`** of the dissimilarity `d`: every
complete run of neighbor joining on a symmetric dissimilarity `D` with zero diagonal and
`|D x y - d x y| < r` for distinct taxa forms exactly the splits of the internal edges of
`(G, ι)`. Atteson's theorem gives this for the path-length metric of a binary phylogenetic tree
with `r` half the shortest internal edge length (`njRecoversWithin_of_le`).
