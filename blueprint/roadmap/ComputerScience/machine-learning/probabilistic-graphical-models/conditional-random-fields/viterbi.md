# The Viterbi variables of a chain CRF

Let $c$ be a chain conditional random field with
a finite nonempty set of states $S$ and weights in a linearly ordered commutative semiring $R$,
and let $x$ be an observation sequence. Write $\phi_t(s)$ for the unary potential of $c$ at $x$
of state $s$ at position $t$, and $\psi_t(s', s)$ for its transition potential from $s'$ to $s$
at step $t$. The Viterbi variables $V_t(s)$, for $t \in \mathbb{N}$ and $s \in S$, are defined
by $V_0(s) = \phi_0(s)$ and

$$V_{t+1}(s) = \Big(\max_{s' \in S} V_t(s') \, \psi_t(s', s)\Big) \, \phi_{t+1}(s).$$

Thus $V_t(s)$ is the largest weight of a label path of length $t + 1$ ending in $s$.
