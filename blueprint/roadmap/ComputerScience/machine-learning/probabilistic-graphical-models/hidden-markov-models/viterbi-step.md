# One step of the tabulated Viterbi recursion for a hidden Markov model

Let $h$ be a hidden
Markov model with states $\{0, \dots, n - 1\}$, where $n \ge 1$, transition weights $a(s', s)$
and emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. Given a vector $v \in R^n$ and
$t \in \mathbb{N}$, the Viterbi step returns the vector in $R^n$ whose entry at state $s$ is

$$\Big(\max_{s'} v_{s'} \, a(s', s)\Big) \, b(s, x_{t+1}).$$
