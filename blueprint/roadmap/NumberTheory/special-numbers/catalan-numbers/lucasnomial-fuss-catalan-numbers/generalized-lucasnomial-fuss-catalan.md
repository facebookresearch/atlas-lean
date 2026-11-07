# Generalized Lucasnomial Fuss–Catalan numbers

Let $P$ be Lucas parameters, that is, nonzero
reals $p$ and $q$ whose Lucas bracket sequence $U_0 = 0$, $U_1 = 1$, $U_{m+2} = pU_{m+1} + qU_m$
satisfies $U_m \ne 0$ for every $m \ge 1$. Write $U_m! = U_1 U_2 \cdots U_m$, and let the
Lucasnomial coefficient $\binom{m}{k}_U$ be $\frac{U_m!}{U_k! \, U_{m-k}!}$ for $k \le m$ and $0$
for $k > m$. For natural numbers $a$, $r$ and $n$, the generalized Lucasnomial Fuss–Catalan number
of $P$ is the real number

$$C_{U,a,r}(n) = \frac{U_r}{U_{(a-1)n+r}} \binom{an+r-1}{n}_U.$$

The source takes $a \ge 2$, $r \ge 1$ and $n \ge 1$. Here $a$, $r$ and $n$ range over all natural
numbers: $a - 1$ and $an + r - 1$ are truncated at $0$, and the quotient is $0$ when
$U_{(a-1)n+r} = 0$.

## Sources

- Ballot, JIS Vol. 21. Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`; source SHA-256 `ca51d34e717a237b02bca4bfa28c57dfc15c81f1276c7634d5abe998d1c48b89`.
