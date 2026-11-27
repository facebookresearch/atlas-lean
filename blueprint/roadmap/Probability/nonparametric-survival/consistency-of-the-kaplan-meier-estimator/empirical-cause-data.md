# Empirical grouped competing-risks data

Let $W_i = ((T_i, J_i), C_i)$, for $i = 0, 1, 2, \dots$, be random triples of an event time $T_i$ and a
censoring time $C_i$ in the grid $\{0, 1, \dots, k - 1\}$ and a cause $J_i$ among $r$ causes. For each
$n$ and each outcome $\omega$, the empirical data are the grouped competing-risks data of the first $n$
subjects at the grid times $0, 1, \dots, k - 1$: subject $i$ is recorded at $\min(T_i, C_i)$, failing
from cause $J_i$ when $T_i \le C_i$ and censored otherwise.
