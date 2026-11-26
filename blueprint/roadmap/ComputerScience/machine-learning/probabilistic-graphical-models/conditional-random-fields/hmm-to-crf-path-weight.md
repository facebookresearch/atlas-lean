# The chain CRF of a hidden Markov model has the same path weights

Let $h$ be a hidden
Markov model with nonnegative weights in a linearly ordered commutative semiring, and let $x$ be
an observation stream. For every $t$ and every state path $z = (z_0, \dots, z_t)$, the weight of
$z$ in the chain CRF of $h$ given $x$ equals the joint weight in $h$ of the state path $z$ and the
observations $x_0, \dots, x_t$.
