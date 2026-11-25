# Rebalancing after deletion from the right subtree

Let $c$ be a color, $L$ a red-black
tree, $k$ a key and $R$ a tree whose root may be double black. If $R$ is a genuine red-black
tree, the result is the genuine node with color $c$, left subtree $L$, key $k$ and right subtree
$R$. Otherwise the double black of $R$ is absorbed first: a double-black empty tree becomes the
empty tree, and a double-black node becomes the black node with the same children and key. The
result is then the right-deficit repair (Fix Right) applied to the color $c$, the sibling $L$, the
key $k$ and the absorbed tree; it may again have a double-black root.
