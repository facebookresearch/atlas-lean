# Viterbi's MAP path

Let $h$ be a hidden Markov model with states $\{0, \dots, n - 1\}$,
where $n \ge 1$, whose weights lie in a linearly ordered commutative semiring $R$, with transition
weights $a(s', s)$, and let $x$ be a sequence of observations. For $t \in \mathbb{N}$, let
$T_0, \dots, T_t \in R^n$ be the tabulated Viterbi variables of $h$ on $x$. The Viterbi path of
length $t + 1$ is the state path $(z_0, \dots, z_t)$ in which $z_t$ is the first state $s$, in the
order $0, \dots, n - 1$, that maximizes $(T_t)_s$, and, for $k < t$, $z_k$ is the first state $s'$
that maximizes $(T_k)_{s'} \, a(s', z_{k+1})$.
