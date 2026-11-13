# Correctness of BUILD

**Correctness of BUILD** (Aho, Sagiv, Szymanski & Ullman 1981; Semple & Steel 2003,
Section 6.4): a set `R` of triplets on a nonempty `S`, none of the degenerate form `xx|x` (which
no tree displays and no cut detects), is displayed by a rooted binary phylogenetic tree on `S`
iff for every subset `S'` of at least two taxa the Aho graph of `R` on `S'` is disconnected.
BUILD splits along the components and recurses; the converse direction builds the tree this
way, splitting along any cut.
