# Greatest common divisors of generalized Fermat numbers

For natural numbers $a$, $b$ and
$k$ write $F_k(a, b) = a^{b^k} + 1$, and let $a, b \ge 2$ and $m$, $n$ be natural numbers. If
$n < m$ and $a$ and $b$ are both even, then $\gcd(F_m(a, b), F_n(a, b)) = 1$. If $n < m$, $a$ is
odd and $b$ is even, then $\gcd(F_m(a, b), F_n(a, b)) = 2$. If $n \le m$ and $b$ is odd, then
$\gcd(F_m(a, b), F_n(a, b)) = F_n(a, b)$.

The source assumes $a, b > 2$ and $0 \le n \le m$; its proof uses only $a, b \ge 2$ and treats
$m > n$ ("Since $m > n$"), and the first two cases fail for $m = n$: for $a = b = 4$ and
$m = n = 0$ the gcd is $\gcd(5, 5) = 5$, and for $a = 3$, $b = 4$ and $m = n = 0$ it is
$\gcd(4, 4) = 4$.

## Sources

- Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*, INTEGERS 26 (2026), Article A77, Proposition 1 (`integers-2026-A77-prop-1`).
