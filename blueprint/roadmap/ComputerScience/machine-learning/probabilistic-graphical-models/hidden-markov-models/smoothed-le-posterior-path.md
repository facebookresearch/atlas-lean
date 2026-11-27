# Posterior path maximizes the posterior at each time

Let $g$ be a hidden Markov model with states $\{0, \dots, n - 1\}$, $n \ge 1$, and weights in a
linearly ordered semifield $K$, let $x_0, x_1, \dots$ be observations and $T \in \mathbb{N}$. At
each time $t \le T$, the state $z_t$ of the [posterior decoding path](posterior-path.md) has the
largest [smoothed weight](smoothed.md): $\gamma_{t, T - t}(s) \le \gamma_{t, T - t}(z_t)$ for
every state $s$.
