# The cache-computing node constructor preserves correct size caches

Let $k$ be a key and
let $L$ and $R$ be order-statistic trees whose cached subtree sizes are correct at every node.
Then the node with key $k$, left subtree $L$ and right subtree $R$, whose root cache is the
cached root size of $L$ plus the cached root size of $R$ plus one, also has correct cached
subtree sizes at every node.
