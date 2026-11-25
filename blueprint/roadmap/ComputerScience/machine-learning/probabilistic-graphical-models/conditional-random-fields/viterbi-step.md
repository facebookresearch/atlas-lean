# One step of the tabulated Viterbi recursion for a chain CRF

Let $c$ be a chain
conditional random field with states $\{0, \dots, n - 1\}$, where $n \ge 1$, and weights in a
linearly ordered commutative semiring $R$, and let $x$ be an observation sequence. Write
$\phi_t(s)$ for the unary potential of $c$ at $x$ of state $s$ at position $t$, and
$\psi_t(s', s)$ for its transition potential from $s'$ to $s$ at step $t$. Given a vector
$v \in R^n$ and $t \in \mathbb{N}$, the Viterbi step returns the vector in $R^n$ whose entry at
state $s$ is

$$\Big(\max_{s'} v_{s'} \, \psi_t(s', s)\Big) \, \phi_{t+1}(s).$$
