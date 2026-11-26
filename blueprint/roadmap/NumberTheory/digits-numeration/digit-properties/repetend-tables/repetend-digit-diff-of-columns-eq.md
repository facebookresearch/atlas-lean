# Matching columns of a two-row repetend table

Let $n$ and $L$ be natural numbers and let
$B$ be the set of integers $c$ with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$
modulo $n$. For $c \in B$ and $k \ge 0$ let $r_k(c) = \lfloor c^{k+1}/n \rfloor \bmod c$, and let
$C_k$ be the multiset of the $r_k(c)$ over $c \in B$. Suppose $B$ has exactly two elements, $b$
and $b' \ne b$, and put $D_k = r_k(b') - r_k(b)$. Then for all $i, j \ge 0$ with $C_i = C_j$,
$D_i = D_j$ or $D_i = -D_j$, and the sum of the elements of $C_i$ equals that of $C_j$.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Lemma 28.
