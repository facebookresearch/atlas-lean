# Uniform distribution of Lucas sequences modulo primes dividing the discriminant

Let $U$
be the Lucas sequence with integer parameters $P$ and $Q$, where the pair $(P, Q)$ is
nondegenerate, and write $\pi(m)$ and $\rho(m)$ for the period and the restricted period of $U$
modulo $m$; for a positive integer $N$ and a residue $r$ modulo $N$, let $c_N(r)$ be the number of
$k < \pi(N)$ with $U_k \equiv r \pmod N$. Let $p$ be a prime with $p \nmid Q$ and
$p \mid P^2 - 4Q$, and put $E = \lfloor \pi(p) / \rho(p) \rfloor$. Then: (i) $\rho(p) = p$,
$\rho(p) \mid \pi(p)$, and $c_p(r) = E$ for every residue $r$ modulo $p$; (ii) if $p \ge 5$, then
for every $i \ge 1$, $\rho(p^i) = p^i$, $\pi(p^i) = p^i E$, and $c_{p^i}(r) = E$ for every residue
$r$ modulo $p^i$; (iii) if $p = 2$, then $P$ is even, and if moreover $P \equiv 2 \pmod 4$, then
for every $i \ge 1$, $\rho(2^i) = 2^i$, and if in addition $Q \equiv 1 \pmod 4$, then
$c_{2^i}(r) = 1$ for every residue $r$ modulo $2^i$; (iv) if $p = 3$, then $3 \mid P^2 - Q$, and
if $9 \nmid P^2 - Q$, then for every $i \ge 1$, $\rho(3^i) = 3^i$ and $c_{3^i}(r) = E$ for every
residue $r$ modulo $3^i$; (v) if $p = 2$ and the $2$-adic valuation of $P$ is $e \ge 2$, then
$\rho(2^i) = 2^{\max(i + 1 - e, 1)}$ for every $i \ge 1$; (vi) if $p = 3$ and the $3$-adic
valuation of $P^2 - Q$ is $d \ge 2$, then $\rho(3^i) = 3^{\max(i + 1 - d, 1)}$ for every $i \ge 1$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.5 (`integers-2024-A36-thm-1-5`).
