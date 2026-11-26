# The unfolding of an MDP has no min nodes

For a finite MDP with a nonempty finite set of actions, a discount $\gamma$, a depth $k$ and a
state $s$, the depth-$k$ unfolding of the MDP from $s$ is a tree with no min (opponent) nodes: it
is built only from leaves, max nodes, chance nodes and affine edges. At depth $0$ it is a leaf; at
positive depth it is a max node over the actions, each followed by an affine edge
$v \mapsto r(s, a) + \gamma v$ for the reward and discount and then a chance node over the next
states.
