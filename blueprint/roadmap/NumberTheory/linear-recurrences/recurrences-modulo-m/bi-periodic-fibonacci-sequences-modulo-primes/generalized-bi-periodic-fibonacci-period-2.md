# Period of a generalized bi-periodic Fibonacci sequence modulo a prime

Let $p$ be an odd
prime and let $a, b, c, d \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, $c \ne 0$, $d \ne 0$, and
$a \ne b$ or $c \ne d$. Let $F : \mathbb{N} \to \mathbb{Z}/p\mathbb{Z}$ satisfy $F_0 = 0$,
$F_1 = 1$ and, for every $n \ge 2$, $F_n = a F_{n-1} + c F_{n-2}$ if $n$ is even and
$F_n = b F_{n-1} + d F_{n-2}$ if $n$ is odd. Put $A = ab + c + d$ and $\Delta = A^2 - 4cd$, and
let $\alpha, \beta \in \mathbb{Z}/p\mathbb{Z}$ satisfy $\alpha + \beta = A$ and
$\alpha \beta = cd$. Let $k$ be the least positive period of $F$: $k > 0$, $F_{n+k} = F_n$ for
all $n$, and $k \le m$ for every $m > 0$ with $F_{n+m} = F_n$ for all $n$. If $\Delta$ is a
nonzero square in $\mathbb{Z}/p\mathbb{Z}$, then $k$ divides $2(p - 1)$, and if moreover
$\alpha$ and $\beta$ are nonzero squares in $\mathbb{Z}/p\mathbb{Z}$, then $k$ divides $p - 1$.

## Sources

- Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021), Article 21.9.4, Theorem, lines 225–226, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex>. It follows from `generalizedBiPeriodicFibonacci_period_dvd_general`, which drops the unused `IsSquare Δ`.
