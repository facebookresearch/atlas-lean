# Double-black deletion yields a valid tree from the structural invariants

Let $\alpha$
be a linearly ordered type and $t$ a red-black tree with keys in $\alpha$ that is ordered,
satisfies the red invariant (no red node has a red child), and is black-height balanced (all
root-to-leaf paths contain the same number of black nodes). Then for every $x \in \alpha$, the
tree obtained by deleting $x$ from $t$ by the double-black method is a valid red-black tree.

The root of $t$ need not be black, since the deletion recolors the root of its result black.
