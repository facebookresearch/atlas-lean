# Simulated annealing step

On a finite state space, for an energy $V$, a proposal kernel $R$ and a temperature $T$, one annealing step from state $x$ draws $y$ from $R(x)$ and moves to $y$ with probability $\min\big(1, e^{-\max(V(y) - V(x), 0)/T}\big)$, otherwise staying at $x$. At $T = 0$ the exponent is $0$ by the convention $x/0 = 0$, so every proposal is accepted.
