# Electrical incidence matrix of an oriented network

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`. The electrical incidence matrix is the real `V × E` matrix with
entries

`A(n, e) = [tail(e) = n] − [head(e) = n]`,

where `[P]` is `1` if `P` holds and `0` otherwise: column `e` has `+1` at the tail and `−1` at the
head. It is the negation of the signed graph incidence, which has `+1` at the head and `−1` at the
tail. A branch whose tail and head coincide has a zero column.
