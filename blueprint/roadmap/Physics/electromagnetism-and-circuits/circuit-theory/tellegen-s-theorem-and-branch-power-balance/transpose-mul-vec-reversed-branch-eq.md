# Reversing a branch negates only its potential-defined voltage

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`, let `A` be the
[electrical incidence matrix](electrical-incidence.md), `φ` real node potentials and `e₀` a branch.
Reversing the branch `e₀` swaps its tail and head, giving the network with `tail'(e₀) = head(e₀)`,
`head'(e₀) = tail(e₀)` and the other branches unchanged, and electrical incidence `A'`. Then `A'ᵀ φ`
is `Aᵀ φ` with its entry at `e₀` negated: the potential-defined voltage of `e₀` changes sign and
every other branch voltage is unchanged.
