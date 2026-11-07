# Least multiples in $S(U)$ and the orbit lcm $L(n)$

Let $P$ and $Q \ne 0$ be integers and
$U$ the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and $U_{k+2} = P U_{k+1} - Q U_k$. Let
$\pi_U(m)$ be the period of $U$ modulo $m$ and $\pi_U^i$ its $i$-th iterate, with
$\pi_U^0(m) = m$. Let $S(U)$ be the set of positive integers $m$ coprime to $Q$ with
$\pi_U(m) \mid m$, let $S'(U)$ be the set of $m \in S(U)$ with $m \mid U_1 + \dots + U_m$, and
say that a natural number $x$ has integral averages if $x \mid w_1 + \dots + w_x$ for every
integer sequence $(w_k)_{k \ge 0}$ with $w_{k+2} = P w_{k+1} - Q w_k$ for all $k$. Let $n > 0$.
If the period orbit of $n$ closes at some step $k$, meaning that $\pi_U^i(n)$ is coprime to $Q$
for all $i \le k$ and $\pi_U^{k+1}(n) = \pi_U^j(n)$ for some $j \le k$, then the least element of
$S(U)$ divisible by $n$ is $L(n) = \operatorname{lcm}(\pi_U^0(n), \dots, \pi_U^{\omega(n)}(n))$,
where $\omega(n)$ is the least such $k$. Moreover, if $c$ is the least element of $S(U)$
divisible by $n$, and either $P - Q - 1 \ne 0$ and $\gcd(c, P - Q - 1) = 1$, or $P - Q - 1 = 0$
and $\gcd(c, Q - 1) = 1$, then $c$ is also the least element of $S'(U)$ divisible by $n$, and $c$
has integral averages.

In the paper's notation $a = P$ and $b = -Q$, so $P - Q - 1 = a + b - 1$ and $Q - 1 = -b - 1$;
the paper's hypothesis $\gcd(n, b) = 1$ is the case $i = 0$ of the closing condition.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.8 (`integers-2024-A36-thm-2-8`).
