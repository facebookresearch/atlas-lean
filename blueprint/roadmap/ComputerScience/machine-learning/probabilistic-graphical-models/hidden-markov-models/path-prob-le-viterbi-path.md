# The Viterbi path is a most probable path

Let $h$ be a hidden Markov model with states
$0, \dots, n - 1$, where $n \ge 1$, and nonnegative weights in a linearly ordered commutative
semiring, and let $x_0, x_1, \dots$ be observations. For every $t \in \mathbb{N}$ and every state
path $z = (z_0, \dots, z_t)$, the joint weight of $z$ and $x_0, \dots, x_t$ is at most the joint
weight of the Viterbi path of length $t + 1$ and $x_0, \dots, x_t$.
