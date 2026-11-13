# Death of the unpadded sequence from $1, \dots, N$ for $N = 3$, $4$ or $N \ge 10$

Let
$N$ be a natural number with $N = 3$, $N = 4$ or $N \ge 10$, and let $B_N$ be the sequence with
initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without padding by the recurrence
$B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$. Then $B_N$ dies: there is
a natural number $T$ such that $B_N(1), \dots, B_N(T)$ can be computed and $B_N(T + 1)$ cannot,
because the recurrence refers to a nonpositive index or to an index not yet computed.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1 (`jis-2024-24.7.4-thm-1`).
