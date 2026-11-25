# The electrical incidence is the negated graph incidence

Let `V` be a finite set of nodes and `E` a finite set of branches, each branch `e` with a tail node
`tail(e)` and a head node `head(e)`. The [electrical incidence matrix](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md) is
the negation of the signed graph incidence `G`, whose entries are
`G(n, e) = [head(e) = n] − [tail(e) = n]`: `A = −G`. This is the definition of `A`.
