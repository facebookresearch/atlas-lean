# Length of the unpadded sequence from $1, \dots, N$

For every natural number $N \ge 14$,
the sequence $B_N$ with initial conditions $B_N(i) = i$ for $1 \le i \le N$, continued without
padding by the recurrence $B_N(n) = B_N(n - B_N(n-1)) + B_N(n - B_N(n-2)) + B_N(n - B_N(n-3))$,
has exactly $N + 24$ terms: $B_N(1), \dots, B_N(N + 24)$ can be computed and $B_N(N + 25)$
cannot, because the recurrence refers to a nonpositive index or to an index not yet computed.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 1 (`jis-2024-24.7.4-thm-1`).
