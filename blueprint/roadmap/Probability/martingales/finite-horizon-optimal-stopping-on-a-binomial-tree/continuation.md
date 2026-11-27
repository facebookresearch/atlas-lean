# One-period continuation value on a binary tree

For a binary tree whose nodes are histories of moves (most recent move first), real numbers $p$ (branch weight) and $\delta$ (discount) and a value function $V$ on nodes, the one-period continuation value at node $s$ is $\delta\,\bigl(p\, V(\text{up} :: s) + (1 - p)\, V(\text{down} :: s)\bigr)$. For $p \in [0, 1]$ and $\delta \ge 0$ it is the discounted expected value one period later.
