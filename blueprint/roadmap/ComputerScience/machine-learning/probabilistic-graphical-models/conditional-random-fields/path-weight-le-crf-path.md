# The Viterbi path of a chain CRF has maximal weight

For a chain conditional random field
with states $0, \dots, n - 1$ where $n \ge 1$, weights in a linearly ordered commutative
semiring, and an observation stream $x$, for every $t$ and every label path $z$ of length
$t + 1$, the weight of $z$ is at most the weight of Viterbi's MAP path of length $t + 1$.
