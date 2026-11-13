# Forbidden differences 1 and q and windowed adjacent-swap permutations

For all natural
numbers $q$, $n$ and $k$, the number of $k$-subsets of $\{1, \dots, n\}$ in which no two
distinct elements differ by $1$ or by $q$ equals the number of permutations $\pi$ of
$\{0, 1, \dots, n\}$ such that $|\pi(i) - i| \le 1$ for every $i$; for every $i_0 \ge 0$ with
$i_0 + q \le n + 1$, all $i, j$ with $i_0 \le i, j < i_0 + q$ satisfy
$\pi(i) \le \pi(j) + q$ (every window of $q$ consecutive values has maximum minus minimum
at most $q$); and $\pi$ has exactly $k$ excedances (points $i$ with $\pi(i) > i$).

The paper takes $q \ge 2$; for $q \le 1$ the statement reduces to the case $Q = \{1\}$. The
condition $|\pi(i) - i| \le 1$ cannot be dropped: for $q = n = 2$ all $6$ permutations of
$\{0, 1, 2\}$ satisfy the window condition, while only $3$ subsets of $\{1, 2\}$ have no two
elements differing by $1$ or $2$.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Theorem 8.
