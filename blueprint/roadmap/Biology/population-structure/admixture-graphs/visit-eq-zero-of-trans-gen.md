# Visit eq zero of trans Gen

Acyclicity, transitive form: if `Y` is an ancestor of `X`, meaning `Y` is reached from
`X` by repeatedly passing from a node to one of its parents, then a lineage starting from
`Y` never passes through the descendant `X`, so `visit Y X = 0`.
