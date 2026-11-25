# The Viterbi variables of a hidden Markov model

Let $h$ be a hidden Markov model with a
finite nonempty set of states $S$, initial weights $\pi(s)$, transition weights $a(s', s)$ and
emission weights $b(s, o)$ in a linearly ordered commutative semiring $R$, and let
$x_0, x_1, \dots$ be a sequence of observations. The Viterbi variables $V_t(s)$, for
$t \in \mathbb{N}$ and $s \in S$, are defined by $V_0(s) = \pi(s) \, b(s, x_0)$ and

$$V_{t+1}(s) = \Big(\max_{s' \in S} V_t(s') \, a(s', s)\Big) \, b(s, x_{t+1}).$$

When all weights are nonnegative, $V_t(s)$ is the largest joint weight of a state path of length
$t + 1$ ending in $s$ and the observations $x_0, \dots, x_t$.
