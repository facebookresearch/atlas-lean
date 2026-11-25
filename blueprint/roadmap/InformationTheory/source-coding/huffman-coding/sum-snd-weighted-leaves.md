# Leaf weights add up to the total weight

Let $t$ be a Huffman tree: a full binary tree whose leaves carry symbols and natural-number weights, not
necessarily a tree returned by Huffman's algorithm. The total weight of $t$ is defined recursively: a leaf
has its own weight, and a tree with left subtree $L$ and right subtree $R$ has the total weight of $L$ plus
that of $R$. The weights of the leaves of $t$, one for each leaf, add up to the total weight of $t$.
