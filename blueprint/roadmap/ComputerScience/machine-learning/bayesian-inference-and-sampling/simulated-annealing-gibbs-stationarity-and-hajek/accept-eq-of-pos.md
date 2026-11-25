# Acceptance probability at positive temperature

Let $S$ be a finite state space with a proposal kernel $R$ (for each state $s$, a probability mass function $R(s, \cdot)$ on $S$) and an energy $V : S \to \mathbb{R}$. The acceptance probability of a move $x \to y$ at temperature $T$ is $\min\big(1, \exp(-\max(V(y) - V(x), 0)/T)\big)$ in $[0, \infty]$. For every $T > 0$ and all states $x, y$, the minimum with $1$ is inactive:

$$\mathrm{accept}_T(x, y) = \exp\!\Big(-\frac{\max(V(y) - V(x),\, 0)}{T}\Big).$$
