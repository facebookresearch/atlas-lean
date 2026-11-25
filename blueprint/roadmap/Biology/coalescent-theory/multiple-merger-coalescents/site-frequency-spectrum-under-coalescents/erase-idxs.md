# Removing the entries at a set of positions from a list

For a finite set `K` of natural numbers, a list `l` of natural numbers and a natural number `k`,
the result is the list of the entries of `l`, in their order, whose positions do not lie in `K`,
the positions being numbered `k, k + 1, …` from the first entry of `l`. An element of `K` below
`k` or at least `k + |l|` matches no entry and removes nothing; for the empty list the result is
empty. In its use for [merging blocks](merge-set.md), `k = 0`, and in the jump chain `K` is a set
of positions of `l`.
