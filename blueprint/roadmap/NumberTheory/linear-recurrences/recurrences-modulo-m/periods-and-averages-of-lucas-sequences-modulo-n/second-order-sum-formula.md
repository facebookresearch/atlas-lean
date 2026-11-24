# Sum formula for second-order recurrences

Let $P, Q$ be integers with $Q \ne 0$ and
$P^2 - 4Q \ne 0$, let $U = U(P, Q)$ be their Lucas sequence, write $a = P$ and $b = -Q$, and let
$w$ be an integer sequence with $w_{k+2} = a w_{k+1} + b w_k$ for all $k \ge 0$. For $n \ge 0$
let $B(n) = w_1 + \dots + w_n$, and for $n > 0$ let $\pi_U(n)$ be the period of $U$ modulo $n$:
the least $r > 0$ with $U_r \equiv 0$ and $U_{r+1} \equiv 1 \pmod n$, or $0$ if there is none.
If $a + b - 1 \ne 0$, then for every $n \ge 0$

$$(a + b - 1) B(n) = w_{n+1} - w_1 + b (w_n - w_0),$$

and for every $n > 0$ coprime to $b$ and every $r \ge 0$ divisible by $\pi_U(n)$, $n$ divides
$w_{r+1} - w_1 + b (w_r - w_0)$. If $a + b - 1 = 0$, then for every $n \ge 0$

$$(-b - 1) B(n) = (w_1 - w_0) U_{n+1} - n (w_1 + b w_0) + w_0 - w_1.$$

The congruence $K(s) \equiv 0 \pmod n$ claimed in part (ii) of the source, for the source's
quantity $K(s)$, is false as printed and is omitted: for $(a, b) = (-6, 7)$, $w = U$ and $n = 3$
one has $\gcd(3, 7) = 1$ and $\pi_U(3) = 2$, but $K(2) = 40$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.2.
