# Tabulated likelihood of a hidden Markov model

For a hidden Markov model $h$ with states
$0, \dots, n - 1$ and weights in a semiring, observations $x_0, x_1, \dots$ and $t \in \mathbb{N}$,
the tabulated likelihood at time $t$ is the sum $\sum_{s < n} v_s$ of the entries of the forward
table $v = (v_0, \dots, v_{n-1})$ at time $t$.

The forward table is computed step by step with $O(n^2)$ semiring operations per step, so the
tabulated likelihood costs $O(t n^2)$ operations; it equals the likelihood of $x_0, \dots, x_t$.
