# Integer sequences with quadratic and linear Fibonacci coefficients

Let $F_n$ be the
$n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e$, the number
$w_n = (an^2 + bn + c)F_n + (dn + e)F_{n-1}$ is an integer for every natural number $n$ if and
only if $e$ is an integer and there are integers $z_1, z_2, z_3, z_4$ with
$a = (2z_1 - z_2 - 2z_3 + z_4)/10$, $b = (-56z_1 - 7z_2 + 66z_3 - 23z_4)/50$,
$c = (48z_1 + 6z_2 - 28z_3 + 9z_4)/25$ and $d = (-6z_1 + 18z_2 - 9z_3 + 2z_4)/25$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - e$,
$z_3 = w_3 - e$ and $z_4 = w_4 - 2e$.

## Sources

- Kálmán Liptai, László Németh, Tamás Szakács and László Szalay, *On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4, Theorem 2.3 (`fq-2024-szakacs06212024rev-thm-2.3`).
