# Deterministic finite-horizon control problem

A problem with $N$ stages
$t = 0, \dots, N - 1$, states in $S$ and actions in $U$: at stage $t$ in state $s$ the admissible
actions form a nonempty finite set $A_t(s) \subseteq U$, an action $a$ leads to the state
$F_t(s, a)$ at the real cost $c_t(s, a)$, and a state $s$ reached at stage $N$ costs $g(s)$.
