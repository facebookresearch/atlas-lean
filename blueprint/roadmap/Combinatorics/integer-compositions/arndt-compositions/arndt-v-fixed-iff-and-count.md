# Compositions fixed by $V$ and their Fibonacci count

A composition $(c_1, \dots, c_m)$
of $n$ is fixed by the map $V$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is odd and
at least $3$ for every even $i$. Let $c_V(n)$ be the number of compositions of $n$ fixed by $V$.
Then $c_V(n) = c_V(n - 2) + c_V(n - 4)$ for every $n \ge 5$, $c_V(1) = c_V(4) = 1$,
$c_V(2) = c_V(3) = 0$, and $c_V(2j) = c_V(2j + 1) = F_{j-1}$ for every $j \ge 1$, where $F$ is
the Fibonacci sequence with $F_0 = 0$ and $F_1 = 1$.

## Sources

- Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26 (2026), Article A64, Proposition 2.
