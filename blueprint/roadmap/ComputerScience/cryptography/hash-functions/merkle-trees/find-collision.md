# Finding a collision from a forged inclusion proof

Given a list of leaves, a position $i$, a claimed leaf $x$ and a path $p$, the search walks up in
lockstep from $x$ with $p$ and from the actual leaf $i$ with its authentication path, and returns the
first pair of unequal hash inputs with equal outputs. It returns nothing when $i$ is not a leaf
position or when no collision appears.
