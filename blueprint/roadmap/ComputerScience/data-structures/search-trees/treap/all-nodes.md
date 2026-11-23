# Treap predicate holding at every node

Let $p$ be a predicate on a key, a value and a
natural-number priority. A tree satisfies $p$ at every node when $p(k, v, n)$ holds for the key
$k$, value $v$ and priority $n$ of each of its nodes. By recursion, this holds for the empty
tree, and holds for a node exactly when it holds for the left subtree, $p$ holds at the node's
key, value and priority, and it holds for the right subtree.
