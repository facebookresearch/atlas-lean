# Every Eulerian trail spells a string with the same `k`-mer multiset

**Every Eulerian trail spells a string with the same `k`-mer multiset** (`2 ≤ k`): if `W` is a
walk of `(k-1)`-mers whose steps are a permutation of the edge occurrences of the de Bruijn
multigraph of `s`, then the `k`-mers of the spelled string are a permutation of those of `s`.
(The empty walk is allowed: it is a trail only when `s` has no `k`-mers, and spells `[]`.)
