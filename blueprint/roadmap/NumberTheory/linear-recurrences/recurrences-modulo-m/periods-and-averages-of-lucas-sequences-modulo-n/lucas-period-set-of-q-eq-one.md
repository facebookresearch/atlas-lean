# Least period and average multiples for $Q = 1$

Let $U$ be the Lucas sequence
$U_0 = 0$, $U_1 = 1$, $U_{j+2} = P U_{j+1} - Q U_j$ with $Q = 1$ and $(P, Q)$ nondegenerate. Let
$S$ be the set of positive integers $m$ coprime to $Q$ such that the period of $U$ modulo $m$
divides $m$, and $S'$ the set of $m \in S$ with $m \mid U_1 + \cdots + U_m$. For $n \ge 1$ let
$C(n)$ and $C'(n)$ be the least elements of $S$ and of $S'$ divisible by $n$, when they exist.
Call $m$ *integral for all recurrences* if every integer sequence $w$ with
$w_{j+2} = P w_{j+1} - Q w_j$ for all $j \ge 0$ satisfies $m \mid w_1 + \cdots + w_m$. Then:

(i) $C(n)$ exists for every $n \ge 1$, and for $n > 1$ one has $C(n) > 1$ and some prime divides
both $C(n)$ and $6(P^2 - 4)$;

(ii) if $n_1$ is odd and every prime dividing $n_1$ divides $P - 2$, then
$C(n_1) = C'(n_1) = n_1$ and $n_1$ is integral for all recurrences; and if $n \ge 1$ and $C(n)$
is odd, then $n$ is odd, $C'(n) = C(n)$, and $C(n)$ is integral for all recurrences;

(iii) if $P$ is odd, then for every $n \ge 1$, $C'(n) = C(n)$ and $C(n)$ is integral for all
recurrences;

(iv) if $P \equiv 0 \pmod 4$ and $n \ge 1$, then $C'(n) = 2C(n)$ and $2C(n)$ is integral for
all recurrences when $C(n) \equiv 2 \pmod 4$, and $C'(n) = C(n)$ and $C(n)$ is integral for all
recurrences when $4 \mid C(n)$;

(v) if $P \equiv 2 \pmod 4$ and $n \ge 1$, then $C'(n)$ does not exist when $C(n)$ is even, and
it does not exist when $n$ is even or $\gcd(n, P + 2) > 1$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.25 (`integers-2024-A36-thm-2-25`).
