# Entries of the electrical incidence matrix

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail
node `tail(e)` and a head node `head(e)`. For every node `n` and branch `e`, the entry of the
[electrical incidence matrix](electrical-incidence.md) is

`A(n, e) = [tail(e) = n] − [head(e) = n]`,

with `[P]` equal to `1` if `P` holds and `0` otherwise: `+1` at the tail, `−1` at the head, and
`0` at every node when tail and head coincide.
