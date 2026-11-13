# Selection is indexing into the inorder traversal

For a binary tree $t$ and a natural
number $i$, selecting index $i$ in $t$ gives the same result as looking up zero-based position
$i$ of the inorder traversal of $t$: the entry at that position when $i$ is less than the length
of the traversal, and nothing otherwise.
