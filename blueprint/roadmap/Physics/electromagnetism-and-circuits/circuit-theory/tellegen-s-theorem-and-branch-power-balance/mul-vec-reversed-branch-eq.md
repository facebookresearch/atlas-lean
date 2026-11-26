# Reversing a branch and its current leaves node currents unchanged

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`, let `A` be the
[electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md) and `i` real branch currents, and let `e₀` be
a branch. Reversing the branch `e₀` swaps its tail and head, giving the network with
`tail'(e₀) = head(e₀)`, `head'(e₀) = tail(e₀)` and the other branches unchanged, and electrical
incidence `A'`. Let `i'` be `i` with the current of `e₀` negated, `i'(e₀) = −i(e₀)`. Then
`A' i' = A i`: the node current sums, and so the node injections that balance them, are unchanged.
