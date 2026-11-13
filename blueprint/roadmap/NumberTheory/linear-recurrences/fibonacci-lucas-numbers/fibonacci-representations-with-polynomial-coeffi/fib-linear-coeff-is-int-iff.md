# Integer sequences with linear Fibonacci coefficients

Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d$, the number $w_n = (an + b)F_n + (cn + d)F_{n-1}$ is an integer for every
natural number $n$ if and only if $d$ is an integer and there are integers $z_1, z_2, z_3$ with
$a = (-z_1 - 3z_2 + 2z_3)/5$, $b = (6z_1 + 3z_2 - 2z_3)/5$ and $c = (-2z_1 + 4z_2 - z_3)/5$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - d$ and
$z_3 = w_3 - d$.

## Sources

- Kálmán Liptai, László Németh, Tamás Szakács and László Szalay, *On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4, Theorem 2.1.
