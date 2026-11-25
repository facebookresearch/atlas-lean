# A loop branch has a zero incidence column

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`. If a branch `e` is a loop, `tail(e) = head(e)`, then the column
of `e` in the [electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md) is zero: `A(n, e) = 0` for
every node `n`.
