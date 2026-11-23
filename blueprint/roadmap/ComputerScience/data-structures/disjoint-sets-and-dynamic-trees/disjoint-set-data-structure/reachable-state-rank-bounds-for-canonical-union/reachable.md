# Array union-find structures built by the public operations

For the union-find structure stored as parent and rank arrays, consider the structures obtained from
an empty structure of any initial capacity by appending a new singleton node, by find with path
compression, and by union of the sets of two nodes. The raw linking of two nodes, which accepts a
first node that is not a root, is not among these operations. This is the family of
[union-find structures built by make-set, find and union](../reachable.md) for this second
implementation of union-find.
