# Period-seven pattern of the padded sequence from $1, \dots, N$

Let $N \ge 72$ be a
natural number, and let $B$ be the sequence with $B(n) = 0$ for $n \le 0$ and $B(i) = i$ for
$1 \le i \le N$, continued by the recurrence $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$.
Let $\nu = -1, -2, -2, -2, 2, 1, 0$ according as $N \equiv 0, 1, 2, 3, 4, 5, 6 \pmod 7$. Then
for all natural numbers $k \ge 1$ and $r < 7$ with $N + 67 \le N + 7k + r \le 2N + \nu$, the
term $B(N + 7k + r)$ can be computed, and it equals $7k + 2$, $N + 7k + 2$, $N + 7k + 4$, $7$,
$2N + 2k + 45$, $2N + k - 7$ or $N - 2$ according as $r = 0, 1, 2, 3, 4, 5$ or $6$.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Theorem 2 (`jis-2024-24.7.4-thm-2`).
