# The expected number of correct states is a sum of posteriors

Let $g$ be a hidden Markov model with states $\{0, \dots, n - 1\}$ and weights in a semifield $K$,
let $x_0, x_1, \dots$ be observations and $T \in \mathbb{N}$. For every state path
$z = (z_0, \dots, z_T)$, the [posterior expected number of correctly decoded states](expected-correct.md)
of $z$ is the sum over $t = 0, \dots, T$ of the [smoothed weight](smoothed.md)
$\gamma_{t, T - t}(z_t)$ of the state $z_t$ at time $t$.
