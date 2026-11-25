# A potential-defined branch voltage is tail minus head potential

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`, let `φ` be real node potentials and `v` real branch voltages
given by the potentials through the transpose of the
[electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md) `A`, `v = Aᵀ φ`. Then for every branch `e`

`v(e) = φ(tail(e)) − φ(head(e))`.
