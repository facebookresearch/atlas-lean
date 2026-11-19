# Posterior decoding

Let $g$ be a hidden Markov model with states $\{0, \dots, n - 1\}$, $n \ge 1$, and weights in a
linearly ordered semifield $K$, let $x_0, x_1, \dots$ be observations and $T \in \mathbb{N}$. The
posterior decoding path $(z_0, \dots, z_T)$ takes at each time $t \le T$ the first state $s$, in
the order $0, \dots, n - 1$, that maximizes the [smoothed weight](smoothed.md)
$\gamma_{t, T - t}(s)$.
