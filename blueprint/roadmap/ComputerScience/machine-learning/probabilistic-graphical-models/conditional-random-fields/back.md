# Backpointer of the tabulated CRF Viterbi algorithm

Let $c$ be a chain CRF with states
$\{0, \dots, n-1\}$, where $n \ge 1$, and weights in a linearly ordered commutative semiring
$R$, and let $\psi_t(s', s)$ be its transition potential from $s'$ to $s$ at step $t$ given the
observation sequence $x$. For a step $t$, a table $v \in R^n$ and a state $s$, the backpointer
of $s$ is the first state $s'$, in the order $0, \dots, n-1$, that maximizes
$v_{s'} \, \psi_t(s', s)$.
