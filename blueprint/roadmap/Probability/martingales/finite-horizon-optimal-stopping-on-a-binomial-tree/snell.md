# Snell envelope by backward induction

On a binary tree with up probability $p$ and discount factor $\delta$, for a path-dependent exercise payoff $g$ on histories, the Snell envelope with $k$ periods left at node $s$ is $g(s)$ when $k = 0$ and otherwise $\max\bigl(g(s), \text{discounted continuation value of the envelope with } k - 1 \text{ periods left}\bigr)$: the value of the optimal stopping problem by backward induction.
