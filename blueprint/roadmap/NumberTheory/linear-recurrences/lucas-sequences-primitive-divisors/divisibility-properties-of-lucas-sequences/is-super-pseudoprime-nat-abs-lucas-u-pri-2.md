# Super strong Lucas pseudoprimes from composed Lucas pairs

Let $P_1, Q_1$ be integers
with $\gcd(P_1, Q_1) = 1$ such that the Lucas pair $(P_1, Q_1)$ is nondegenerate, with Lucas
sequences $U_n(P_1, Q_1)$, $V_n(P_1, Q_1)$ and discriminant $D_1 = P_1^2 - 4Q_1$. Let $k \ge 2$
with $\gcd(D_1, k) = 1$, let $\varepsilon = \pm 1$, and let $P = \varepsilon V_k(P_1, Q_1)$,
$Q = Q_1^k$ and $D = P^2 - 4Q$. Let $p$ be a prime with $p \nmid k D_1$ and $\gcd(p, PQD) = 1$,
such that $p \ge 5$ if $D > 0$, $p \ge 11$ if $D < 0$, and $p \ne 13$ if $|P_1| = 1$ and
$Q_1 = 2$. Then $\gcd(P, Q) = 1$, the Lucas pair $(P, Q)$ is nondegenerate,
$D = D_1 U_k(P_1, Q_1)^2$, and $|U_p(P, Q)|$ is a super strong Lucas pseudoprime with parameters
$P, Q$; if moreover $Q_1 = \pm 1$, it is also a super Frobenius pseudoprime with parameters
$P, Q$. Finally, $2^{\omega(k)} \le \tau(k) \le \tau(|U_p(P, Q)|)$, where $\omega(k)$ is the
number of distinct prime factors of $k$ and $\tau(n)$ is the number of positive divisors of $n$.

The source writes the exclusion as "$p \ne 13$ if $P = \pm 1$, $Q = 2$", which is vacuous for
$Q = Q_1^k$ with $k \ge 2$; read for $(P, Q)$ it fails: $(P_1, Q_1, k) = (1, 2, 2)$ gives
$(P, Q) = (\mp 3, 4)$ and $|U_{13}(3, 4)| = 181$, a prime. Without $\gcd(p, PQD) = 1$, the
standing hypothesis of Theorem 5.1, it fails as well: $(P_1, Q_1, k, p) = (-3, -1, 3, 5)$ gives
$D = 1300$ and $5 \mid U_5(\pm 36, -1)$.

## Sources

- Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*, INTEGERS 25 (2025), Article A107, Theorem 5.1 (iv).
