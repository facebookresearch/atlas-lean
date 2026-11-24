# Incidence matrix of the series DC motor loop

The ground-deleted incidence matrix of the series motor loop is the 3 × 4 matrix with rows
`(-1, 1, 0, 0)`, `(0, -1, 1, 0)` and `(0, 0, -1, 1)`: entry `+1` where the node is the head of the
branch and `-1` where it is the tail. The nodes are `0` (supply terminal), `1`
(resistance–inductance junction) and `2` (inductance–back-EMF junction). The branches, as
(head, tail), are `0` the supply source (ground, node `0`), `1` the armature resistance (node `0`,
node `1`), `2` the armature inductance (node `1`, node `2`) and `3` the back-EMF source (node `2`,
ground).
