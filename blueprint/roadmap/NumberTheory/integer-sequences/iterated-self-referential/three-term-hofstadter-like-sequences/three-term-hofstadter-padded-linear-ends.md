# Length of the padded sequence from $1, \dots, N$

Let $N$ be a natural number, and let
$t = 196, 2087, 3201, 4315, 200, 32478, 118$ and $e = 27, 254, 524, 560, 20, 4547, 9$
according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Let $B$ be the sequence with $B(n) = 0$
for $n \le 0$ and $B(i) = i$ for $1 \le i \le N$, continued by the recurrence
$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$. If $N \ge t$, then $B$ ends after
exactly $2N + e$ terms: $B(1), \dots, B(2N + e)$ can be computed and $B(2N + e + 1)$ cannot,
because the recurrence refers to an index not yet computed.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2 (`jis-2024-24.7.4-thm-2`).
