# Simulated annealing step

For an energy $V$, a proposal kernel $R$ and temperature $T$, one annealing step from state $x$ draws $y$ from $R(x)$ and moves to $y$ with probability $\min\big(1, e^{-\max(V(y) - V(x), 0)/T}\big)$, otherwise staying at $x$.
