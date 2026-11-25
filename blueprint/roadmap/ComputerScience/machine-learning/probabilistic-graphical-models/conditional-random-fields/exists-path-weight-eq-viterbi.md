# The Viterbi variables of a chain CRF are attained

Let $c$ be a chain CRF with a finite
nonempty set of states $S$ and weights in a linearly ordered commutative semiring, and let $x$
be an observation sequence. For every $t \in \mathbb{N}$ and every state $s \in S$ there is a
label path $z = (z_0, \dots, z_t) \in S^{t+1}$ with $z_t = s$ whose path weight equals the
Viterbi variable of $s$ at time $t$.
