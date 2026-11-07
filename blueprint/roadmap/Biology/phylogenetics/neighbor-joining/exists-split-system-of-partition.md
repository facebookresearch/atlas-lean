# The path metric on a partition into sides

Let `S` partition the taxa of a binary
phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w` and path-length metric `d` into
sides of edges. Then there is a system of splits `A e` (`e : E`) of the set of clusters with
positive weights `w' e`, closed under complement, pairwise compatible, binary, and containing
every trivial split, such that
* the weight of every internal split (both sides with at least two clusters) is the length of an
  edge with both endpoints internal;
* a split whose side is `{s, t}` comes from an edge with side `s ∪ t`;
* for taxa `x ∈ s` and `y ∈ t` of distinct clusters, `d x y` is half the total weight of the
  splits separating `s` from `t`, plus a term `ρ s x` depending only on `s` and `x` and a term
  `ρ t y`.
In the construction, the splits are those of the edges that cut no cluster.
