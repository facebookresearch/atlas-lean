# Law of simulated annealing

Let $S$ be a finite state space with proposal distributions $R(x)$ and energy $V$. One annealing step at temperature $T$ from $x$ proposes $y \sim R(x)$, moves to $y$ with probability $\min\{1, \exp(-\max(V(y) - V(x), 0)/T)\}$ and otherwise stays at $x$; at $T = 0$ this probability is $1$, by the convention $x/0 = 0$. For a temperature schedule $T : \mathbb{N} \to \mathbb{R}$ and a start $x_0$, the law of $X_k$ is the point mass at $x_0$ for $k = 0$, and the law of $X_{k+1}$ is obtained from the law of $X_k$ by one annealing step at temperature $T(k+1)$.
