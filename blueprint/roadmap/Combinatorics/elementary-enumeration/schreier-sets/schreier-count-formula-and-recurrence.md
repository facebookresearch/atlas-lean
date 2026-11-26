# Closed formula and recurrence for Schreier counts

Let $p$ and $q$ be positive integers,
and write $|S^{p/q}_n|$ for the number of $(p, q)$-Schreier sets with maximum $n$. For every
natural number $n$,

$$|S^{p/q}_n| = \sum_{i=1}^{\lfloor (n+1)q/(p+q) \rfloor} \binom{n - \lceil pi/q \rceil}{i - 1},$$

and for every $n \ge p + q + 1$,

$$|S^{p/q}_n| = \sum_{i=1}^{q} (-1)^{i+1} \binom{q}{i} |S^{p/q}_{n-i}| + |S^{p/q}_{n-(p+q)}|.$$

The printed initial-term formula has $\lceil ni/q \rceil$ in place of $\lceil pi/q \rceil$, which is
false (for $p = 1$, $q = 2$, $n = 2$ one has $|S^{1/2}_2| = 2$ but the printed sum is $1$);
$\lceil pi/q \rceil$ is the paper's own formula (Section 3, equation for $|S^{p/q}_n|$). The
corollary states the formula for $1 \le n \le p + q$; it holds for every $n$, so the range
restriction is dropped.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 2 (`jis-2026-26.2.2-cor-2`).
