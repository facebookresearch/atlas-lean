# Compositions fixed by $U$ and their Padovan count

A composition $(c_1, \dots, c_m)$ of
$n$ is fixed by the map $U$ if and only if $c_i = 1$ for every odd $i$ and $c_i$ is even for
every even $i$. Let $c_U(n)$ be the number of compositions of $n$ fixed by $U$. Then
$c_U(n) = c_U(n - 2) + c_U(n - 3)$ for every $n \ge 4$, $c_U(1) = 1$, $c_U(2) = 0$,
$c_U(3) = 1$, and $c_U(n) = P_{n-1}$ for every $n \ge 1$, where $P$ is the shifted Padovan
sequence, given by $P_0 = 1$, $P_1 = 0$, $P_2 = 1$ and $P_{j+3} = P_{j+1} + P_j$.

## Sources

- Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26 (2026), Article A64, Proposition 1.
