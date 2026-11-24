# The inorder traversal begins with the leftmost key

Let $t$ be a nonempty tree with
cached heights and $m$ its leftmost key. Then the inorder traversal of $t$ is $m$ followed by the
inorder traversal of the tree obtained from $t$ by removing its leftmost key.

The leftmost key is computed by a function that takes a default value for the empty tree; the
identity holds for every choice of default.
