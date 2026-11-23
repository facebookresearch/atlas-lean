# Conditional probabilities of a chain CRF are nonnegative

Let $c$ be a chain CRF with a
finite set of states $S$ and weights in a linearly ordered field $R$, and let $x$ be an
observation sequence. For every $t \in \mathbb{N}$ and every label path
$z = (z_0, \dots, z_t) \in S^{t+1}$, the conditional probability of $z$ given $x$ is nonnegative.

No positivity of the partition function is assumed; nonnegativity comes from the nonnegativity
of the potentials.
