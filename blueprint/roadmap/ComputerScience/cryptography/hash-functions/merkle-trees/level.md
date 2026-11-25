# Next level of a Merkle tree

For a two-to-one hash $h : A \times A \to A$, the next level of a list of nodes hashes adjacent pairs
and promotes an unpaired last node unchanged: $[a, b, c, d, e] \mapsto [h(a, b), h(c, d), e]$.
