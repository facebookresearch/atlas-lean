# Backward-induction values

The values $V_t(s)$ of a deterministic control problem for
$t = N, N - 1, \dots, 0$: $V_N = g$ and
$V_t(s) = \min_{a \in A_t(s)} \bigl(c_t(s, a) + V_{t+1}(F_t(s, a))\bigr)$ for $t < N$.
