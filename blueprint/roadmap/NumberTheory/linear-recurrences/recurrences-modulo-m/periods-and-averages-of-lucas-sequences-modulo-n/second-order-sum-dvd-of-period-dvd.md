# Sums of a second-order recurrence over whole periods

Let $P, Q$ be integers with $Q \ne 0$,
let $U = U(P, Q)$ be their Lucas sequence, write $a = P$ and $b = -Q$, and suppose
$a + b - 1 \ne 0$. Let $n > 0$ be coprime to $b(a + b - 1)$, and let $\pi_U(n)$ be the period of
$U$ modulo $n$: the least $r > 0$ with $U_r \equiv 0$ and $U_{r+1} \equiv 1 \pmod n$, or $0$ if
there is none. Then $\pi_U(n) > 0$, and for every $r \ge 0$ divisible by $\pi_U(n)$ and every
integer sequence $w$ with $w_{k+2} = a w_{k+1} + b w_k$ for all $k \ge 0$, $n$ divides
$w_1 + \dots + w_r$.

Part (ii) of the corollary is false as printed and is omitted: for $(a, b) = (-6, 7)$, so that
$a + b - 1 = 0$, the number $n = 3$ is coprime to $7 \cdot (-8)$ and $\pi_U(3) = 2$, but
$U_1 + U_2 = 1 - 6 = -5$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.2.
