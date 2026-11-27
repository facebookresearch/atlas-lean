# Snell envelope by backward induction

On a binary tree with real branch weight $p$ and real discount $\delta$, for a path-dependent exercise payoff $g$ on histories, the Snell envelope with $k$ periods left at node $s$ is $g(s)$ when $k = 0$ and otherwise $\max\bigl(g(s), \text{continuation value of the envelope with } k - 1 \text{ periods left}\bigr)$. For $p \in [0, 1]$ and $\delta \ge 0$ it is the value of the optimal stopping problem by backward induction.
