# Admissible sequence of a deterministic control problem

States
$x_0, \dots, x_N \in S$ and actions $u_0, \dots, u_{N-1} \in U$ form an admissible sequence from
state $s$ at stage $t \le N$ when $x_t = s$ and, for every stage $i$ with $t \le i < N$,
$u_i \in A_i(x_i)$ and $x_{i+1} = F_i(x_i, u_i)$. Entries before stage $t$ are unconstrained.
