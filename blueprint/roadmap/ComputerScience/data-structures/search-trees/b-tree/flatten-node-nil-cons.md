# Flattening a keyless node, one child at a time

For a raw B-tree $c$ and a list $C$ of
raw B-trees, the flattening of the node with no keys and child list $c$ followed by $C$ is the
flattening of $c$ followed by the flattening of the node with no keys and child list $C$.

This covers nodes with more children than a well-formed node would have.
