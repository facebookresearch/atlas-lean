# Five-cycle lemma for the three-term Hofstadter-like recurrence

Let $K \ge 3$ be a
natural number, $\mu \ge 1$ an integer, and $a_4, \dots, a_K$ arbitrary integers. Let $B$ be
the sequence given by $B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$, padded with
$B(n) = 0$ for $n \le 0$, with initial conditions
$1, 2, 3, a_4, \dots, a_K, K + \mu, 3, K + 3, K + \mu + 1, 5$ at the indices $1, \dots, K + 5$.
Then for all natural numbers $k$ and $r < 5$ with
$K + 1 \le K + 5k + r \le K + \lfloor (5\mu - 15)/2 \rfloor$, the term $B(K + 5k + r)$ can be
computed, and it equals $5$, $K + 3k + \mu$, $3$, $K + 5k + 3$ or $K + 3k + \mu + 1$ according
as $r = 0, 1, 2, 3$ or $4$.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 5, citing the author's thesis, Proposition 9.10 (`jis-2024-24.7.4-lem-5`).
