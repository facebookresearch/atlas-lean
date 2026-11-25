# Digit differences between the rows $b_1$ and $b_1^5$ of the order-$6$ table

Let
$p \equiv 1 \pmod 6$ be prime, $k \ge 1$, $t \in \{1, 2\}$ and $n = t p^k$, and let $b_1 < n$
have multiplicative order $6$ modulo $n$. Put $H = 0$ if $t = 1$, $H = p^k$ if $t = 2$ and
$b_1 < p^k$, and $H = -p^k$ if $t = 2$ and $b_1 \ge p^k$. Let $b_5 = b_1^5 \bmod n$ and, for
$i \ge 0$, $D_i = r_i(b_5) - r_i(b_1)$, where $r_i(c) = \lfloor c^{i+1}/n \rfloor \bmod c$. Then
$D_0 = D_5 = 0$, $D_2 = n - b_1 - (b_1^2 \bmod n) = 1 - 2 b_1 + n - H$,
$n D_1 = (n - H) D_2$, $D_3 = D_2$ and $n D_4 = H D_2$.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Lemma 36.
