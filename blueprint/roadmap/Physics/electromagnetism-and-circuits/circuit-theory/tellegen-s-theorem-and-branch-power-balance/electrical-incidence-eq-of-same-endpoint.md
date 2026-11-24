# Branches with the same endpoints have equal incidence columns

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`. If two branches `e₁` and `e₂`, distinct or not, have the same
tail and the same head, `tail(e₁) = tail(e₂)` and `head(e₁) = head(e₂)`, then their columns in the
[electrical incidence matrix](electrical-incidence.md) are equal: `A(n, e₁) = A(n, e₂)` for every
node `n`. Parallel branches thus keep distinct columns only through their branch index.
