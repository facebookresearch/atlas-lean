# Bounding-sphere invariant of a ball tree

Validity of a ball tree is defined inductively:
the empty tree and every leaf are valid, and a node with center $c$ and squared-radius bound $b$
is valid when both of its subtrees are valid and every point in the point list of either subtree
lies within squared Euclidean distance $b$ of $c$.
