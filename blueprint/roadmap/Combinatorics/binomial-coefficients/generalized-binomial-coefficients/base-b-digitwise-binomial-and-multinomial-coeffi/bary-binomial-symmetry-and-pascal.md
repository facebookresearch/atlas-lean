# Symmetry and Pascal's recurrence for $b$-ary binomial coefficients

Let $b \ge 2$. For a
natural number $m$ write $m_i = \lfloor m / b^i \rfloor \bmod b$ for its $i$-th base-$b$ digit.
For integers $m$ and $j$, let $C_b(m, j) = \prod_{i=0}^{m+j} \binom{m_i}{j_i}$ if $m \ge 0$ and
$j \ge 0$, and $C_b(m, j) = 0$ otherwise. Then for all integers $n$ and $k$ with $0 < n$ and
$0 \le k \le n$, we have $C_b(n, k) = C_b(n, n - k)$, and if $C_b(n, k) \ne 0$ then
$C_b(n, k) = C_b(n - 1, k - 1) + C_b(n - 1, k)$.

## Sources

- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (Symmetry and recurrence), equation (label `eq:recurrence`), lines 432–445, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
