# Least multiples of $2^k n_1$ in the period set for even $P$

Let $U$ be the Lucas sequence
$U_0 = 0$, $U_1 = 1$, $U_{j+2} = P U_{j+1} - Q U_j$ with nondegenerate parameters
$P, Q \in \mathbb{Z}$. Let $S$ be the set of positive integers $m$ coprime to $Q$ such that the
period of $U$ modulo $m$ divides $m$, and let $S'$ be the set of $m \in S$ with
$m \mid U_1 + \cdots + U_m$. Call $m$ *integral for all recurrences* if every integer sequence
$w$ with $w_{j+2} = P w_{j+1} - Q w_j$ for all $j \ge 0$ satisfies $m \mid w_1 + \cdots + w_m$.

Suppose $P - Q - 1 \ne 0$, $P$ is even and $Q \equiv 1 \pmod 4$. Let $n = 2^k n_1$ with
$k \ge 1$ and $n_1 > 1$ odd, and suppose $P \equiv -2$ and $Q \equiv 1$ modulo every prime
dividing $n_1$. Then every prime dividing $n_1$ divides $P^2 - 4Q$, and $n$ is the least element
of $S$ divisible by $n$. If $P \equiv 2 \pmod 4$, no element of $S'$ is divisible by $n$. If
$P \equiv 0 \pmod 4$, then for $k = 1$ the least element of $S'$ divisible by $n$ is $2n$, and
$2n$ is integral for all recurrences; for $k \ge 2$ the least element of $S'$ divisible by $n$
is $n$, and $n$ is integral for all recurrences.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.20 (`integers-2024-A36-thm-2-20`).
