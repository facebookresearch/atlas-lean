# Detailed balance implies stationarity

Let $P$ be a stochastic matrix on the finite state
space $\{0, 1, \dots, M\}$ and let $\pi$ be a probability distribution on the same states. If
$\pi$ and $P$ satisfy the detailed balance equations $\pi(i) P(i, j) = \pi(j) P(j, i)$ for all
states $i, j$, then $\pi$ is stationary for $P$: $\sum_i \pi(i) P(i, j) = \pi(j)$ for every
state $j$.
