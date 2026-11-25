# Path weights of a chain CRF are bounded by the Viterbi variables

For a chain conditional
random field with a nonempty finite set of states, weights in a linearly ordered commutative
semiring, and an observation stream $x$, for every $t$ and every label path
$z = (z_0, \dots, z_t)$, the weight of $z$ is at most the Viterbi variable at time $t$ of its last
state $z_t$.
