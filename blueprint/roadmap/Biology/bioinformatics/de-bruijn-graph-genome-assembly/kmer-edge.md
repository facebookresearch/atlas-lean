# De Bruijn edge of a k-mer

The edge of the de Bruijn multigraph contributed by a `k`-mer `w`: from its prefix
`(k-1)`-mer `w.dropLast` to its suffix `(k-1)`-mer `w.tail`.
