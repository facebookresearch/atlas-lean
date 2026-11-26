# State of the anti-recurrence construction

Let $a = (a_1, \dots, a_k)$ be a finite list of
natural numbers. The state at step $0$ is the pair of the empty list and the empty set. If the
state at step $n$ has set $S$, then the state at step $n + 1$ is the pair $(\beta, S')$, where
$\beta = (x_1, \dots, x_k)$ is the mex block of length $k$ from $S$ (each $x_j$ is the least
positive integer not in $S \cup \{x_1, \dots, x_{j-1}\}$) and
$S' = S \cup \{x_1, \dots, x_k\} \cup \{a_1 x_1 + \dots + a_k x_k\}$.

In the notation of the source, for $n \ge 1$ the block at step $n$ is
$(B_{(n-1)k+1}, \dots, B_{nk})$ and the set at step $n$ is
$\{B_1, \dots, B_{nk}\} \cup \{A_1, \dots, A_n\}$, where the $B_m$ are the non-anti-recurrence
numbers and the $A_m$ are the anti-recurrence numbers of $a$.

## Sources

- Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026), Article A24, Section 2 (definition of anti-recurrence sequences and Lemma 2).
