# Maximum high endpoint at a node

For subtrees $L$ and $R$ and an entry $e$, the node
maximum is the largest of the high endpoint of the interval of $e$, the cached maximum high
endpoint stored at the root of $L$, and the one stored at the root of $R$, where an empty subtree
stores no cached maximum and contributes nothing.
