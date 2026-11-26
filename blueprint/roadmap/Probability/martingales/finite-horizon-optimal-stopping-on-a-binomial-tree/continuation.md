# One-period continuation value on a binary tree

For a binary tree whose nodes are histories of moves (most recent move first), an up probability $p$, a discount factor $\delta$ and a value function $V$ on nodes, the one-period continuation value at node $s$ is $\delta\,\bigl(p\, V(\text{up} :: s) + (1 - p)\, V(\text{down} :: s)\bigr)$: the discounted expected value one period later.
