# Divisibility and multiplicativity of the orbit lcm

Let $P$ and $Q \ne 0$ be integers and
$U$ the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and $U_{k+2} = P U_{k+1} - Q U_k$. Let
$\pi_U(m)$ be the period of $U$ modulo $m$ and $\pi_U^i$ its $i$-th iterate, with
$\pi_U^0(m) = m$. Say that $\omega(m)$ exists if the period orbit of $m$ closes at some step $k$,
meaning that $\pi_U^i(m)$ is coprime to $Q$ for all $i \le k$ and $\pi_U^{k+1}(m) = \pi_U^j(m)$
for some $j \le k$; then $\omega(m)$ is the least such $k$ and
$L(m) = \operatorname{lcm}(\pi_U^0(m), \dots, \pi_U^{\omega(m)}(m))$. Then:
(i) if $n > 0$, $\omega(n)$ exists and $m \mid n$, then $\omega(m)$ exists and $L(m) \mid L(n)$;
(ii) if $n > 0$, $g > 0$, $\omega(n)$ exists and $g \mid \pi_U^i(n)$ for some $i$, then
$\omega(g)$ exists and $L(g) \mid L(n)$;
(iii) if $r, s > 0$ are coprime and $\omega(r)$ and $\omega(s)$ exist, then $\omega(rs)$ exists
and $L(rs) = \operatorname{lcm}(L(r), L(s))$;
(iv) if $p$ is prime, $i \ge 1$ and $\omega(p)$ exists, then $\omega(p^i)$ exists and
$L(p^i) = \operatorname{lcm}(p^i, L(p))$.

In the paper's notation $b = -Q$. The coprimality to $b$ of $n$, $r$, $s$ and $p$ is part of the
existence of $\omega$; the existence of $\omega(g)$ in (ii) and of $\omega(rs)$ in (iii) is
implicit in the paper's statements about $L(g)$ and $L(rs)$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Corollary 2.4 (`integers-2024-A36-cor-2-4`).
