# Properties of the rank of appearance in a Lucas sequence

Let $U = U(P, Q)$ be the Lucas
sequence with integer parameters $P$ and $Q \ne 0$, let $D = P^2 - 4Q$, let $\rho(m)$ be the rank
of appearance of $m$ in $U$, and write $(a/n)$ for the Jacobi symbol. Let $r$ and $s$ range over
positive integers and $p$ over primes. Then:
(i) if $\gcd(r, Q) = 1$, then $r \mid U_s$ if and only if $\rho(r) \mid s$;
(ii) if $p$ is odd and $p \nmid Q$, then $p \mid U_{p - (D/p)}$;
(iii) if $p \mid D$ and $p \nmid Q$, then $\rho(p) = p$;
(iv) if $p \nmid 2QD$, then $p \mid U_{(p - (D/p))/2}$ if and only if $(Q/p) = 1$;
(v) if $p$ is odd, $p \nmid Q$, and $k \ge 0$ satisfies $\rho(p^k) = \rho(p)$ and
$\rho(p^{k+1}) \ne \rho(p)$, then $\rho(p^j) = p^{\max(j - k, 0)} \rho(p)$ for every $j \ge 1$;
(vi) if $\gcd(rs, Q) = 1$ and $r \mid s$, then $\rho(r) \mid \rho(s)$;
(vii) if $\gcd(P, Q) = 1$, then $\gcd(U_r, U_s) = |U_{\gcd(r, s)}|$;
(viii) if $\gcd(r, s) = 1$ and $\gcd(rs, Q) = 1$, then
$\rho(rs) = \operatorname{lcm}(\rho(r), \rho(s))$;
(ix) if $\gcd(P, Q) = 1$ and $p \mid Q$, then $p \nmid U_n$ for every $n \ge 1$;
(x) if $\gcd(P, Q) = 1$, $p$ is odd and $p \nmid Q$, then $p \equiv (D/p) \pmod{\rho(p)}$.

Part (v) fails for $p = 2$: for $(P, Q) = (1, -1)$ one has $\rho(2) = 3$, $\rho(4) = 6$ and
$\rho(8) = 6 \ne 12$.

## Sources

- Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*, INTEGERS 25 (2025), Article A107, Theorem 2.4.
