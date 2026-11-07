# Structure of the pseudo-greedy expansion of a rational

Let $p$ and $q$ be positive
integers, let $r = p/q$, and let $(x_n)$, $(a_n)$ and $(\varepsilon_n)$ be the remainder
sequence, the pseudo-greedy expansion and the gap sequence of $r$. Put
$d_n = q a_0 a_1 \cdots a_{n-1}$ (so $d_0 = q$). Then there are positive integers $c_n$ and
integers $e_n$ ($n \ge 0$) such that for every $n$ we have $x_n = c_n / d_n$,
$\varepsilon_n = e_n / c_n$, $e_n \equiv d_n \pmod{c_n}$, $-c_n/2 \le e_n < c_n/2$,
$a_n = (d_n - e_n)/c_n + 1$, $c_{n+1} = c_n - e_n$ and $d_{n+1} = d_n a_n$. Moreover, as
$n \to \infty$, $c_n = O(a_0 \cdots a_{n-1} / a_n)$ and $c_n = O(1.5^n)$.

## Sources

- Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*, INTEGERS 26 (2026), Article A28, Lemma 4 (`integers-2026-A28-lem-4`).
