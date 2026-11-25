# The backtracked path of a chain CRF attains the Viterbi variable

For a chain conditional
random field with states $0, \dots, n - 1$ where $n \ge 1$, weights in a linearly ordered
commutative semiring, and an observation stream $x$, for every $t$ and every state $s$ the weight
of the backtracked path of length $t + 1$ ending in $s$, obtained by following the backpointers,
equals the Viterbi variable at time $t$ of $s$.
