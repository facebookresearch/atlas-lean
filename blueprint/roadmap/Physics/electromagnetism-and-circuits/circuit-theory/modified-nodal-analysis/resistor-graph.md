# Graph of the nodes joined by resistor branches

Let `n_N` nodes and `n_B` branches be numbered, each branch `e` with a tail node `tail(e)` and a
head node `head(e)`, and let `R` be a set of resistor branches. The resistor graph is the simple
graph on the nodes in which two distinct nodes `u` and `v` are adjacent when some resistor branch
joins them in either direction: `tail(e) = u` and `head(e) = v`, or `tail(e) = v` and `head(e) = u`,
for some `e ∈ R`.
