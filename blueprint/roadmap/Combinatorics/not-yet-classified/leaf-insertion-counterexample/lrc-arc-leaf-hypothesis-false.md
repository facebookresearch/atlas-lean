# Lrc arc leaf Hypothesis false

The leaf-insertion hypothesis for arcs is false: it is not true that for every self-avoiding
walk `cons h q` from `a`, adding `a` to the support of `q` keeps the complement connected. The
witness is the walk from `(1, 0)` around the ring `lrc_ringS` from `(1, 1)` to `(1, -1)`; adding
`(1, 0)` closes the ring and isolates the origin (`lrc_leafRemovable_false`). An induction over
arcs that assumes this hypothesis therefore proves nothing.
