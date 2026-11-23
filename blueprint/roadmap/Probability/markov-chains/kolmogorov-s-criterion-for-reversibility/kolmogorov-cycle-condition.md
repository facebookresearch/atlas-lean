# Kolmogorov's cycle condition

A stochastic matrix $P$ on the finite state space
$\{0, 1, \dots, M\}$ satisfies Kolmogorov's cycle condition when (1) for all states $x, y$,
$P(x, y) > 0$ implies $P(y, x) > 0$; and (2) for every $n \ge 0$ and every loop of states
$x_0, x_1, \dots, x_n$ with $x_n = x_0$ and $\prod_{i=0}^{n-1} P(x_{i+1}, x_i) > 0$, we have
$\prod_{i=0}^{n-1} P(x_i, x_{i+1}) = \prod_{i=0}^{n-1} P(x_{i+1}, x_i)$.
