# Erdős Problem 369, location variant

This is the statement that for every real
$\varepsilon > 0$ and every natural number $k \ge 2$ there is a natural number $N$ such that for
every natural number $n \ge N$ there is a natural number $a$ with $\lfloor n/2 \rfloor \le a + 1$
and $a + k \le n$ for which every prime factor $p$ of each of the $k$ consecutive integers
$a + 1, \dots, a + k$ satisfies $p \le n^\varepsilon$.

Erdős Problem 369 as written allows the run anywhere in $\{1, \dots, n\}$, which is trivially
true (take $1, \dots, k$ once $n^\varepsilon \ge k$); here the run must start at or after
$\lfloor n/2 \rfloor$.
