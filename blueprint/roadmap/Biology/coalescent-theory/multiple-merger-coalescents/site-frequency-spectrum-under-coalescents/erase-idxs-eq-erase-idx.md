# Deleting the largest position first does not shift the others

Let `K` be a finite set of natural numbers with largest element `m`, let `k ≤ m` and let `l` be a
list of natural numbers, with positions numbered from `k`. Removing from `l` the entries at the
positions in `K` gives the same list as first deleting the entry at position `m` (the entry with
index `m - k` from the start, if there is one) and then removing the entries at the positions in
`K \ {m}`, still numbered from `k`.
