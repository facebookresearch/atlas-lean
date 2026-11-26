# Grounded nodal conductance of a connected network is positive definite

Let `n_N` nodes and `n_B` branches be numbered, each branch `e` with a tail node `tail(e)` and a
head node `head(e)`, and let `R` be a set of resistor branches with real resistances `R_e` with
`R_e > 0` for every `e ∈ R`. Suppose that the [resistor graph](resistor-graph.md) is connected, and
let `g` be any node, the ground. Then the [nodal conductance matrix](nodal-conductance.md) with the
row and the column of `g` deleted is positive definite.

This is the conductance case, with weights `1 / R_e`, of the
[positive definiteness of a grounded weighted Laplacian](../../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/grounded-weighted-laplacian-pos-def.md).
