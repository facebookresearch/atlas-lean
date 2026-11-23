# Red-black insertion yields a valid tree from the invariants

Let $\alpha$ be a linearly
ordered type, $x \in \alpha$ a key, and $t$ a red-black tree with keys in $\alpha$ that is
ordered, satisfies the red property (no red node has a red child), and is balanced (every
root-to-leaf path contains the same number of black nodes). Then the tree obtained by inserting
$x$ into $t$ is valid.

The root of $t$ need not be black, since insertion recolors the root black.
