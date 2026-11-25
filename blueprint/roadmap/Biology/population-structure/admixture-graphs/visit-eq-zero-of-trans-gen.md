# A lineage from an ancestor never passes through its descendant

In every [admixture graph](admixture-graph.md), let `Y` be an ancestor of `X`: `Y` is reached from
`X` in one or more steps, each from a node to one of its parents. Then the
[visit probability](visit.md) of `X` from `Y` is `v(Y, X) = 0`: a lineage traced from `Y` toward the
root never passes through its descendant `X`.
