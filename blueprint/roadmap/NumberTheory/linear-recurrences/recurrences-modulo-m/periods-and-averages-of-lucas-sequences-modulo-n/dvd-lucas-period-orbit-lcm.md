# $n$ divides $L(n)$

Let $P, Q$ be integers with $Q \ne 0$ and $U$ the Lucas sequence with
$U_0 = 0$, $U_1 = 1$ and $U_{j+2} = P U_{j+1} - Q U_j$. For $m \in \mathbb{N}$ let $\pi_U(m)$ be
the least $r \ge 1$ with $U_r \equiv 0$ and $U_{r+1} \equiv 1 \pmod m$, or $0$ if there is none,
and let $\pi_U^i$ be its $i$-th iterate, so that $\pi_U^0(m) = m$. Let $\omega(n)$ be the least
$k$ such that $\pi_U^i(n)$ is coprime to $Q$ for all $i \le k$ and $\pi_U^{k+1}(n) = \pi_U^j(n)$
for some $j \le k$, or $0$ if there is no such $k$. Then every $n \in \mathbb{N}$ divides
$L(n) = \operatorname{lcm}(\pi_U^0(n), \pi_U^1(n), \dots, \pi_U^{\omega(n)}(n))$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Remark 2.6.
