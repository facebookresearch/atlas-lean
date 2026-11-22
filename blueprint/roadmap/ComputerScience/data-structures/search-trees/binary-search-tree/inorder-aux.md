# Inorder traversal of a binary tree with an accumulator

For a binary tree $t$ and a list
$s$, the accumulated traversal of the empty tree onto $s$ is $s$, and the accumulated traversal of
a node with key $k$, left subtree $L$ and right subtree $R$ onto $s$ is the accumulated traversal
of $L$ onto the list consisting of $k$ followed by the accumulated traversal of $R$ onto $s$.

Unfolding the recursion, the result is the inorder traversal of $t$ followed by $s$.
