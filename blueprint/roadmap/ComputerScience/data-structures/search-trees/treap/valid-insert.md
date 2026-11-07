# Inserting into a treap preserves validity

Let the keys come from a linear order. If a
tree is a valid treap, that is, its keys are in strict binary-search-tree order and its
priorities are in min-heap order, then for every key $k$, value $v$ and natural-number
priority $q$, the tree obtained by inserting $k$ with value $v$ and priority $q$ is again a
valid treap.
