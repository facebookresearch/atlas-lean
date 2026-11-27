# Path weights of a hidden Markov model are bounded by the Viterbi variables

Let $h$ be a
hidden Markov model with a finite nonempty set of states $S$ and initial weights $\pi$, transition
weights $a$ and emission weights $b$ that are nonnegative elements of a linearly ordered
commutative semiring, and let $x_0, x_1, \dots$ be observations. Let $\delta$ be the Viterbi
variables, $\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s' \in S} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$ and every state path $z = (z_0, \dots, z_t) \in S^{t+1}$, the joint weight of
$z$ and $x_0, \dots, x_t$ is at most $\delta_t(z_t)$.
