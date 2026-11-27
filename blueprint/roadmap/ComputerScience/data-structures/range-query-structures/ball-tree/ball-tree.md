# Ball tree

For a dimension $d$, a ball tree over the integer points $\mathbb{Z}^d$
(functions $\{0, \dots, d-1\} \to \mathbb{Z}$) is either empty, a leaf holding one point,
or a node holding a center point $c \in \mathbb{Z}^d$, a natural number $b$ (the squared-radius
bound of the node's sphere) and two child ball trees.

That the sphere around $c$ actually contains the points below the node is a separate validity
invariant, not part of this definition.
