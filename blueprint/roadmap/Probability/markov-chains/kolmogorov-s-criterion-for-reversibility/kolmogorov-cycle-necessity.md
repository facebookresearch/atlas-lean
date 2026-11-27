# Kolmogorov's cycle theorem, necessity half

Let $P$ be an irreducible stochastic matrix
on the finite state space $\{0, 1, \dots, M\}$. If $P$ is reversible, that is, some probability
distribution $\pi$ is stationary for $P$ and satisfies the detailed balance equations
$\pi(i) P(i, j) = \pi(j) P(j, i)$ for all states $i, j$, then $P$ satisfies Kolmogorov's cycle
condition: (1) for all states $x, y$, $P(x, y) > 0$ implies $P(y, x) > 0$; and (2) for every
$n \ge 0$ and every loop of states $x_0, x_1, \dots, x_n$ with $x_n = x_0$ and
$\prod_{i=0}^{n-1} P(x_{i+1}, x_i) > 0$, we have
$\prod_{i=0}^{n-1} P(x_i, x_{i+1}) = \prod_{i=0}^{n-1} P(x_{i+1}, x_i)$.
