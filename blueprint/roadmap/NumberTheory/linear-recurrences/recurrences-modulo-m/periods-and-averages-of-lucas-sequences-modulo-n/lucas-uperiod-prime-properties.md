# Periods of a Lucas sequence modulo a prime

Let $U = U(P, Q)$ be a nondegenerate Lucas
sequence with discriminant $D = P^2 - 4Q$, and let $p$ be a prime. Write $\pi_U(m)$ and
$\rho_U(m)$ for the least period and the least restricted period of $U$ modulo $m$, and
$\left(\frac{x}{p}\right)$ for the Jacobi symbol.
(i) If $p \nmid 2QD$, then $\rho_U(p) > 1$, $\rho_U(p) \mid p - \left(\frac{D}{p}\right)$,
$\rho_U(p) \mid \pi_U(p)$ and $\pi_U(p) / \rho_U(p) \mid p - 1$; if $p = 2$ and $2 \nmid QD$,
then $\pi_U(2) = 3$.
(ii) If $p \nmid 2QD$, then $\rho_U(p) \mid \left(p - \left(\frac{D}{p}\right)\right) / 2$ if and
only if $\left(\frac{Q}{p}\right) = 1$.
(iii) If $p \nmid Q$ and $p \mid D$, then $\rho_U(p) = p$ and $\pi_U(p) \mid p (p - 1)$.
(iv) If $p \nmid 2Q$ and $\left(\frac{D}{p}\right) = 1$, then $\pi_U(p) \mid p - 1$.
(v) If $p \nmid 2Q$ and $\left(\frac{D}{p}\right) = -1$, then $\pi_U(p) \mid p^2 - 1$ and every
prime factor $\ell$ of $\pi_U(p)$ satisfies $2 \ell \le p + 1$.
(vi) If $p \nmid Q$ and $p \mid D$, then $p \mid \pi_U(p)$ and every prime factor of $\pi_U(p)$
is at most $p$.
(vii) If $p \nmid Q$, there is a largest $c \ge 1$ with $\rho_U(p^c) = \rho_U(p)$. If
$p^c \ne 2$, then $\rho_U(p^i) = p^{\max(i - c, 0)} \rho_U(p)$ for every $i \ge 1$. If
$p^c = 2$, there is a largest $d \ge 2$ with $\rho_U(2^d) = \rho_U(4)$, and
$\rho_U(2^i) = 2^{\max(i + 1 - d, 1)} \rho_U(2)$ for every $i \ge 2$.
(viii) If $p \nmid Q$, there is a largest $e \ge 1$ with $\pi_U(p^e) = \pi_U(p)$. If
$p^e \ne 2$, then $\pi_U(p^i) = p^{\max(i - e, 0)} \pi_U(p)$ for every $i \ge 1$. If
$p^e = 2$, there is a largest $g \ge 2$ with $\pi_U(2^g) = \pi_U(4)$, and
$\pi_U(2^i) = 2^{\max(i + 1 - g, 1)} \pi_U(2)$ for every $i \ge 2$.
(ix) $\rho_U(1) = \pi_U(1) = 1$.

In the paper's notation $W(n + 2) = a W(n + 1) + b W(n)$ one has $a = P$ and $b = -Q$. The claim
$\pi_U(p) / \rho_U(p) \mid p - 1$, printed under "if $p \ge 2$", is stated here under the
hypothesis $p \nmid 2QD$ of (i).

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 1.4 (`integers-2024-A36-thm-1-4`).
