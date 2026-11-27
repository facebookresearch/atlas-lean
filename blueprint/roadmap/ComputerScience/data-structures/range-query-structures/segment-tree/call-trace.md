# Call trace for a segment-tree operation

A trace records an invocation at its root.
It can stop at an empty tree or a pruned internal node (`stop`), stop at a `leaf`, descend
into `one` child (with `true` for the left child), or descend into `both` children in order.
