# Grounded nodal conductance of a connected network is invertible

Let `n_N` nodes and `n_B` branches be numbered, each branch `e` with a tail node `tail(e)` and a
head node `head(e)`, and let `R` be a set of resistor branches with real resistances `R_e` with
`R_e > 0` for every `e ∈ R`. If the [resistor graph](resistor-graph.md) is connected and `g` is any
node, then the [nodal conductance matrix](nodal-conductance.md) with the row and the column of `g`
deleted is invertible: the grounded nodal equations of a connected resistive network have exactly
one solution.
