# Integer sequences with linear Fibonacci coefficients and an alternating term

Let $F_n$
be the $n$-th Fibonacci number and put $F_{-1} = 1$, so that $F_{n-1} = F_{n+1} - F_n$ for every
$n \ge 0$. For rational numbers $a, b, c, d, e, f$, the number
$w_n = (an + b)F_n + (cn + d)F_{n-1} + e + f(-1)^n$ is an integer for every natural number $n$
if and only if there are integers $v_0, \dots, v_5$ with
$a = (3v_0 + 2v_1 - 7v_2 - v_3 + 4v_4 - v_5)/5$,
$b = (-3v_0 - 2v_1 - 3v_2 + 6v_3 + 6v_4 - 4v_5)/5$,
$c = (-4v_0 - v_1 + 11v_2 - 2v_3 - 7v_4 + 3v_5)/5$,
$d = -2v_1 + v_2 + 2v_3 - v_4$,
$e = (v_0 + 3v_1 + v_2 - 3v_3 - v_4 + v_5)/2$ and
$f = (v_0 + v_1 - 3v_2 - v_3 + 3v_4 - v_5)/2$.

These integers are then the initial values of the sequence: $v_i = w_i$ for $0 \le i \le 5$.

## Sources

- Kálmán Liptai, László Németh, Tamás Szakács and László Szalay, *On Certain Fibonacci Representations*, Fibonacci Quarterly 62 (2024), no. 4, Theorem 3.1 (`fq-2024-szakacs06212024rev-thm-3.1`).
