# The Viterbi path of a chain CRF

Let $c$ be a chain CRF with states $\{0, \dots, n-1\}$,
where $n \ge 1$, and weights in a linearly ordered commutative semiring, and let $x$ be an
observation sequence. For $t \in \mathbb{N}$, the Viterbi path of length $t + 1$ is the
backtracked path ending in the first state, in the order $0, \dots, n-1$, that maximizes the
Viterbi table at time $t$.
