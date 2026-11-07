# Closure of the period set under lcm and products

Let $U$ be the Lucas sequence with
parameters $P$ and $Q \ne 0$, given by $U_0 = 0$, $U_1 = 1$ and $U_{k+2} = P U_{k+1} - Q U_k$. Let
$S(U)$ be the set of positive integers $n$ coprime to $Q$ such that the period $\pi_U(n)$ of $U$
modulo $n$ divides $n$, and let $S'(U)$ be the set of $n \in S(U)$ with
$n \mid U_1 + \dots + U_n$. Say that a natural number $x$ has integral averages if
$x \mid w_1 + \dots + w_x$ for every integer sequence $(w_k)_{k \ge 0}$ with
$w_{k+2} = P w_{k+1} - Q w_k$ for all $k$, and that $x$ satisfies the coprimality condition if
either $P - Q - 1 \ne 0$ and $\gcd(P - Q - 1, x) = 1$, or $P - Q - 1 = 0$ and
$\gcd(Q - 1, x) = 1$. Then for all $m, n \in S(U)$, both $\operatorname{lcm}(m, n)$ and $mn$ lie
in $S(U)$, and if $mn$ satisfies the coprimality condition, then each of $m$, $n$,
$\operatorname{lcm}(m, n)$ and $mn$ lies in $S'(U)$ and has integral averages. Moreover, for every
positive integer $r$ and every $c$, if $c$ is the least element of $S(U)$ divisible by $r$ and $c$
satisfies the coprimality condition, then $c$ is also the least element of $S'(U)$ divisible by
$r$, and $c$ has integral averages.

In the paper's notation $a = P$ and $b = -Q$, so $P - Q - 1 = a + b - 1$ and $Q - 1 = -b - 1$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.4 (`integers-2024-A36-thm-2-4`).
