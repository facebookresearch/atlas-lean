# Okasaki's rebalancing

Given a color $c$, red-black trees $l$ and $r$, and a key $k$,
rebalancing produces a tree as follows. Suppose $c$ is black and one of these configurations
occurs, taking the first that applies: $l$ is a red node with a red left child; $l$ is a red node
with a red right child; $r$ is a red node with a red left child; $r$ is a red node with a red
right child. The black root and the two red nodes then hold three keys and leave four subtrees,
which read in inorder as $t_1, x, t_2, y, t_3, z, t_4$. The result is a red node with key $y$, left
child the black node with subtrees $t_1, t_2$ and key $x$, and right child the black node with
subtrees $t_3, t_4$ and key $z$. In every other case the result is the node with color $c$, left
subtree $l$, key $k$ and right subtree $r$.
