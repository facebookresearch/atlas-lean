# The tabulated Viterbi variables of a hidden Markov model

Let $h$ be a hidden Markov model
with states $\{0, \dots, n - 1\}$, where $n \ge 1$, initial weights $\pi(s)$, transition weights
$a(s', s)$ and emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. The Viterbi table assigns to each
$t \in \mathbb{N}$ a vector $T_t \in R^n$: the vector $T_0$ has entry $\pi(s) \, b(s, x_0)$ at
each state $s$, and $T_{t+1}$ is the Viterbi step at time $t$ applied to $T_t$, the vector whose
entry at state $s$ is $\big(\max_{s'} (T_t)_{s'} \, a(s', s)\big) \, b(s, x_{t+1})$.

The entry of $T_t$ at state $s$ is the Viterbi variable of $s$ at time $t$.
