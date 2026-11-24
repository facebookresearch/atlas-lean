# Point update of a segment tree

The point update of a segment tree over an additive
monoid at an index $i \in \mathbb{N}$, relative to the tree's segment, with a value $y$ is
defined recursively. The empty tree stays empty. A leaf becomes a leaf with value $y$ if $i = 0$
and is unchanged otherwise. At an internal node with left child $L$ and right child $R$: if $i$
is less than the size of $L$, then $L$ is replaced by its point update at $i$ with $y$, and
otherwise $R$ is replaced by its point update at $i$ minus the size of $L$ with $y$; the node
keeps its cached length, and its cached aggregate becomes the aggregate of the new left child
plus the aggregate of the new right child.
