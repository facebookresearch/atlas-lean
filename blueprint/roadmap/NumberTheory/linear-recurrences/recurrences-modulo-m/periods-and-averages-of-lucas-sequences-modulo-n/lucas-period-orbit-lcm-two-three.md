# The orbit lcms $L(2)$ and $L(3)$

Let $P$ and $Q \ne 0$ be integers, write $a = P$ and
$b = -Q$, and let $U$ be the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and
$U_{k+2} = P U_{k+1} - Q U_k$. Let $\pi_U(m)$ be the period of $U$ modulo $m$ and $\pi_U^i$ its
$i$-th iterate, with $\pi_U^0(m) = m$. Say that $L(m)$ exists if the period orbit of $m$ closes at
some step $k$, meaning that $\pi_U^i(m)$ is coprime to $Q$ for all $i \le k$ and
$\pi_U^{k+1}(m) = \pi_U^j(m)$ for some $j \le k$; then, with $\omega(m)$ the least such $k$,
$L(m) = \operatorname{lcm}(\pi_U^0(m), \dots, \pi_U^{\omega(m)}(m))$. Then:
(i) if $a$ and $b$ are odd, then $L(2)$ exists if and only if $\gcd(b, 3) = 1$;
(ii) if $a$ is even, then $L(2)$ exists if and only if $b$ is odd;
(iii) if $L(3)$ exists, then $L(3) = 3$ or $6 \mid L(3)$;
(iv) $L(3)$ exists and equals $3$ if and only if $a \equiv b \equiv -1 \pmod 3$;
(v) $L(3)$ exists and is divisible by $6$ if and only if $\gcd(b, 6) = 1$ and not both
$a \equiv -1 \pmod 3$ and $b \equiv -1 \pmod 6$;
(vi) if $a$ is even and $b$ is odd, then $L(2)$ exists and $L(2) = 2$.
In each of the following cases, with all congruences modulo $6$, every $L(m)$ named exists and
has the given value:
(vii) if $a \equiv \pm 1$ and $b \equiv 1$, then $L(2) = L(3) = 24$;
(viii) if $a \equiv 1$ and $b \equiv -1$, or $a \equiv 3$ and $b \equiv 1$, then
$L(2) = L(3) = 6$;
(ix) if $a \equiv -1$ and $b \equiv -1$, then $L(2) = 6$ and $L(3) = 3$;
(x) if $a \equiv 0$, then $L(3) = 6$ when $b \equiv 1$, and $L(3) = 12$ when $b \equiv -1$;
(xi) if $a \equiv 3$ and $b \equiv -1$, then $L(2) = L(3) = 12$;
(xii) if $a \equiv \pm 2$ and $b \equiv 1$, then $L(3) = 24$, and if $a \equiv -2$ and
$b \equiv -1$, then $L(3) = 6$.
Finally, (xiii) if $n > 0$, every prime factor of $n$ divides $6$ and $L(n)$ exists, then every
prime factor of $L(n)$ divides $6$.

The second half of (xii) is false as printed in the paper for $a \equiv 2 \pmod 6$ and is
restricted here to $a \equiv -2 \pmod 6$: for $(a, b) = (2, 5)$, a nondegenerate pair, one has
$\pi_U(3) = 3$, so $L(3) = 3$, in line with (iv).

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.9 (`integers-2024-A36-thm-2-9`).
