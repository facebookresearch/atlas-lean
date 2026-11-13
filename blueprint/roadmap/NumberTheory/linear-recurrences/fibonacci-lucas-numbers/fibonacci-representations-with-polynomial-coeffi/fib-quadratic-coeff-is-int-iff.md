# Integer sequences with quadratic Fibonacci coefficients

Let $F_n$ be the $n$-th Fibonacci
number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every $n \ge 0$. For rational
numbers $a, b, c, d, e, f$, the number
$w_n = (an^2 + bn + c)F_n + (dn^2 + en + f)F_{n-1}$ is an integer for every natural number $n$
if and only if $f$ is an integer and there are integers $z_1, \dots, z_5$ with
$a = (-z_1 + 3z_2 + z_3 - 3z_4 + z_5)/10$,
$b = (-5z_1 - 75z_2 + 15z_3 + 45z_4 - 17z_5)/50$,
$c = (30z_1 + 30z_2 - 10z_3 - 15z_4 + 6z_5)/25$,
$d = (3z_1 - 4z_2 - 3z_3 + 4z_4 - z_5)/10$ and
$e = (-45z_1 + 80z_2 + 15z_3 - 40z_4 + 11z_5)/50$.

The integers $z_i$ are then determined by the sequence: $z_1 = w_1$, $z_2 = w_2 - f$,
$z_3 = w_3 - f$, $z_4 = w_4 - 2f$ and $z_5 = w_5 - 3f$.

## Sources

- Kálmán Liptai, László Németh, Tamás Szakács and László Szalay, *On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4, Theorem 2.2.
