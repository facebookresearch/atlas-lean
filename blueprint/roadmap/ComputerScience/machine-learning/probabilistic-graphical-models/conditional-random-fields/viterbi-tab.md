# The tabulated Viterbi variables of a chain CRF

Let $c$ be a chain conditional random
field with states $\{0, \dots, n - 1\}$, where $n \ge 1$, and weights in a linearly ordered
commutative semiring $R$, and let $x$ be an observation sequence. Write $\phi_0(s)$ for the
unary potential of $c$ at $x$ of state $s$ at position $0$. The Viterbi table assigns to each
$t \in \mathbb{N}$ a vector $T_t \in R^n$: the vector $T_0$ has entry $\phi_0(s)$ at each state
$s$, and $T_{t+1}$ is the Viterbi step at time $t$ applied to $T_t$.

The entry of $T_t$ at state $s$ is the Viterbi variable $V_t(s)$.
