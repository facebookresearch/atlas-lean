# AVL rebalancing step with cost

Rebalancing a tree $T$ returns a tree and a cost, where
heights are the stored heights. If $T$ is empty, or neither subtree of its root is more than one
taller than the other, it returns $T$ unchanged with zero cost. If the left subtree $L$ is more
than one taller than the right subtree, it applies a right rotation, costing $2$ cache writes and
one rotation, when the left child of $L$ is at least as tall as the right child of $L$, and
otherwise a left-right double rotation, costing $3$ cache writes and two rotations. If the right
subtree $R$ is more than one taller than the left subtree, it applies a left rotation, costing
$2$ cache writes and one rotation, when the right child of $R$ is at least as tall as the left
child of $R$, and otherwise a right-left double rotation, costing $3$ cache writes and two
rotations. All other cost counters are zero.
