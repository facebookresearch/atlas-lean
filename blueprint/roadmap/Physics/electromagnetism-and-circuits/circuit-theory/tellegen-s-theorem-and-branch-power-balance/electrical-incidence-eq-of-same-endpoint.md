# Branches with the same endpoints have equal incidence columns

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`. If two branches `e₁` and `e₂`, distinct or not, have the same
tail and the same head, `tail(e₁) = tail(e₂)` and `head(e₁) = head(e₂)`, then their columns in the
[electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
are equal: `A(n, e₁) = A(n, e₂)` for every node `n`. Parallel branches are thus told apart only by
their branch index, not by their columns.
