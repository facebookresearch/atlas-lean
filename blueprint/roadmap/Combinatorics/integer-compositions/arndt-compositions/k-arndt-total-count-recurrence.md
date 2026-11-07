# Recurrences for generalized Arndt counts

Let $a(n, k)$ be the number of generalized
Arndt compositions of $n$ with shift $k$, set $a(m, k) = 0$ for $m < 0$, and note that
$a(0, k) = 1$ counts the empty composition. For every natural number $j$ and every $n \ge 3$,

$$a(n, -j) = a(n - 1, -j) + 2a(n - 2, -j) - a(n - 2 - j, -j),$$

and for every natural number $k$ and every $n \ge 3$,

$$a(n, k) = a(n - 1, k) + a(n - 2, k) - a(n - 3, k) + a(n - 3 - k, k).$$

The paper sets $a(n - 2 - j, -j) = 0$ whenever $n - 2 - j \le 0$; at $n - 2 - j = 0$ that is
false ($j = 1$, $n = 3$: $a(3, -1) = 3$, while $a(2, -1) + 2a(1, -1) - 0 = 4$), and its own
bijection uses the empty composition there. At $n = 2$ the recurrences fail for every shift
(for instance $a(2, k) \ne a(1, k) + 2a(0, k)$), so $n \ge 3$ is assumed.

## Sources

- Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26 (2026), Article A64, Theorem 4 (`integers-2026-A64-thm-4`).
