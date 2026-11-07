# Viterbi computes the MAP value

Let $h$ be a hidden Markov model with a finite nonempty set
of states $S$ and initial weights $\pi$, transition weights $a$ and emission weights $b$ that are
nonnegative elements of a linearly ordered commutative semiring, and let $x_0, x_1, \dots$ be
observations. Let $\delta$ be the Viterbi variables, $\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s' \in S} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$, $\max_{s \in S} \delta_t(s)$ equals the maximum, over all state paths
$z \in S^{t+1}$, of the joint weight of $z$ and $x_0, \dots, x_t$.
