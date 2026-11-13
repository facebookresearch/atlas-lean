# Block word of a Dyck path of height at most $2$

For a Dyck word
$P = P_0 P_1 \cdots P_{2n-1}$ of semilength $n$, with steps indexed from $0$, the block word of
$P$ is the Boolean word of length $n - 1$ (empty when $n = 0$) whose entry $i$, for
$0 \le i < n - 1$, is true exactly when $P_{2i+1} = U$.

When $P$ has height at most $2$ and $n \ge 1$, it factorizes as $P = U X_1 \cdots X_{n-1} D$
with each $X_{i+1} = P_{2i+1} P_{2i+2}$ a $1$-peak $UD$ or a $0$-valley $DU$, so entry $i$ is
true for a $1$-peak and false for a $0$-valley.

## Sources

- Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.3.2, Section 3, factorization (1).
