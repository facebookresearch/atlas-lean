# Likelihood of the observations

For a hidden Markov model $h$ with a finite set of states
$S$ and weights in a semiring, observations $x_0, x_1, \dots$ and $t \in \mathbb{N}$, the
likelihood of $x_0, \dots, x_t$ is the sum, over all state paths
$z = (z_0, \dots, z_t) \in S^{t+1}$, of the joint weight of $z$ and $x_0, \dots, x_t$.
