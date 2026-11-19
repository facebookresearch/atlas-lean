# The Viterbi variables are attained

Let $h$ be a hidden Markov model with a finite
nonempty set of states $S$ and weights in a commutative semiring $R$ with a linear order, and let
$x$ be an observation sequence. For every time $t$ and every state $s$, there is a state path
$z = (z_0, \dots, z_t)$ with $z_t = s$ whose joint weight with the observations
$x_0, \dots, x_t$ equals the Viterbi variable $V_t(s)$.

No nonnegativity of the weights and no compatibility of the order with the operations is
needed.
