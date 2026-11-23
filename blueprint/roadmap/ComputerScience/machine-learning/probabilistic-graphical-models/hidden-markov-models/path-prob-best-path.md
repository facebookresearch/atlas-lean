# The backtracked path of a hidden Markov model attains the Viterbi variable

Let $h$ be a
hidden Markov model with states $0, \dots, n - 1$, where $n \ge 1$, initial weights $\pi$,
transition weights $a$ and emission weights $b$ in a commutative semiring with a linear order, and
let $x_0, x_1, \dots$ be observations. Let $\delta$ be the Viterbi variables,
$\delta_0(s) = \pi(s)\, b(s, x_0)$ and
$\delta_{t+1}(s) = \bigl(\max_{s'} \delta_t(s')\, a(s', s)\bigr)\, b(s, x_{t+1})$. For every
$t \in \mathbb{N}$ and every state $s$, the joint weight of $x_0, \dots, x_t$ and the backtracked
path of length $t + 1$ ending in $s$, obtained by following the backpointers, equals
$\delta_t(s)$.
