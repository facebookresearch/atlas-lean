# Formal U

The non-backtracking transition matrix of the quotient graph, indexed by
its oriented edges (the dart orbits). The entry at `(e, e')` is `1` when `e'`
starts where `e` ends and `e'` is not the reversal of `e`, and `0` otherwise
(`formalU_apply`); it is not symmetric in general. It takes finite dart
stabilizers only because it reads the endpoints from
`quotientDegeneracyData`.
