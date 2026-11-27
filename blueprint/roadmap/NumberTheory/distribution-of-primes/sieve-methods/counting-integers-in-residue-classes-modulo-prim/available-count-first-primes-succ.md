# Recurrence for the number of available integers

Let $k \ge 1$, let $p_1, \dots, p_{k+1}$
be the first $k + 1$ primes, and let $r_1, \dots, r_{k+1}$ be any natural numbers. For $m = k$ and
$m = k + 1$, call an integer $n$ free if $n \not\equiv r_i \pmod{p_i}$ for every $i \le m$, and
available if $n \equiv r_i \pmod{p_i}$ for at most one $i \le m$; let $\mathrm{av}(m)$ and
$\mathrm{free}(m)$ be the numbers of available and of free integers $n$ with
$1 \le n \le p_1 \cdots p_m$. Then
$\mathrm{av}(k+1) = (p_{k+1} - 1) \cdot \mathrm{av}(k) + \mathrm{free}(k)$.

## Sources

- Florian Pausinger, "Counting Appearances of Integers in Sets of Arithmetic Progressions", Lemma 4.
