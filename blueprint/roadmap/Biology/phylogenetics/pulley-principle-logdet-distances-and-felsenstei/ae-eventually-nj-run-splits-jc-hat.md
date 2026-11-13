# Statistical consistency of neighbor joining under Jukes–Cantor

**Statistical consistency of neighbor joining under Jukes–Cantor** (Saitou & Nei 1987;
Atteson 1999). Let `(G, ι)` be a binary phylogenetic `X`-tree with path-length metric `d` for
edge lengths `w`, and let the sites be pairwise independent and identically distributed, with
the two-leaf marginals of the JC model with rate `μ` and uniform root: for every path `p` from
`x` to `y`, `ℙ(site x = i, site y = j) = jcPath μ (lengths of p) i j / 4`. If neighbor joining
recovers the tree within some radius `r > 0` of the scaled metric `μ d` (for `μ > 0`, Atteson's
theorem gives `r = μ m / 2`, `m` the shortest internal edge length), then almost surely, for all
long enough alignments, every complete run of neighbor joining on the JC-corrected empirical
distances returns exactly the splits of the internal edges of the tree.
