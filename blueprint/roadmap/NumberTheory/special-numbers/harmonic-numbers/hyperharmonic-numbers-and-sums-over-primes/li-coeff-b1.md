# Li's coefficients $b_1(r, m, j, k)$

These rational numbers, indexed by natural numbers
$r, m, j, k$, are defined by recursion on $r$ from Li's coefficients $c$, $d$, $c_1$ and $d_1$.
All values $b_1(0, m, j, k)$ are $0$, $b_1(1, 0, 0, 2) = 1$, and all other values
$b_1(1, m, j, k)$ are $0$. For $s \ge 1$ let $G = \lfloor (s-1)/2 \rfloor$ and
$b(m, j, k) = b_1(s, m, j, k)$; then $b_1(s+1, m, j, k)$ is $0$ except in the following cases.

If $s$ is odd: for $k = 0$ the value is $\sum_{l=m}^{G} b(l, j, 2)\, c_1(l, m)$ when
$1 \le m \le G$ and $j \le G - m$, and $\sum_{l=0}^{G-j} b(l, j, 2)\, c_1(l, 0)$ when $m = 0$ and
$j \le G$. For $k = 1$ the value is $\sum_{l=m-1}^{G-1} b(l, j, 3)\, c(l, m)$ when
$1 \le m \le G$ and $j \le G - m$, and $S_1 + S_2 + b(0, j, 3) - S_3$ when $m = 0$ and $j \le G$,
where $S_1$ is the sum of $b(m', j_1, 2)\, d_1(m', j - j_1)$ over the pairs of natural numbers
$(m', j_1)$ with $m' \le G$, $j_1 \le G - m'$, $j_1 < j$ and $j - j_1 \le m'$,
$S_2 = \sum_{m'=0}^{G-j} b(m', j, 2)\, d_1(m', 0)$, and $S_3$ is the sum of
$b(m', j_1, 3)\, d(m', j - j_1)$ over the pairs with $m' < G$, $j_1 < G - m'$, $j_1 < j$ and
$j - j_1 \le m' + 1$.

If $s$ is even: for $k = 2$ the value is $\sum_{l=m-1}^{G} b(l, j, 0)\, c(l, m)$ when
$1 \le m \le G + 1$ and $j \le G + 1 - m$, and $-T_1 + T_2 + b(0, j, 0) + T_3$ when $m = 0$ and
$j \le G + 1$, where $T_1$ is the sum of $b(m', j_1, 0)\, d(m', j - j_1)$ over the pairs of
natural numbers $(m', j_1)$ with $m' \le G$, $j_1 \le G - m'$, $j_1 < j$ and $j - j_1 \le m' + 1$,
$T_2$ is the sum of $b(m', j, 1)\, d_1(m', 0)$ over $0 \le m' \le \max(G - j, 0)$, and $T_3$ is
the sum of $b(m', j_1, 1)\, d_1(m', j - j_1)$ over the pairs with $m' \le G$, $j_1 \le G - m'$,
$j_1 < j$ and $j - j_1 \le m'$. For $k = 3$ the value is $\sum_{l=m}^{G} b(l, j, 1)\, c_1(l, m)$
when $1 \le m \le G$ and $j \le G - m$, and $\sum_{l=0}^{G-j} b(l, j, 1)\, c_1(l, 0)$ when
$m = 0$ and $j \le G$.

In particular $b_1(r, m, j, 0) = b_1(r, m, j, 1) = 0$ for odd $r$,
$b_1(r, m, j, 2) = b_1(r, m, j, 3) = 0$ for even $r$, and $b_1(r, m, j, 3) = 0$ for odd $r$ when
$m + j = \lfloor (r-1)/2 \rfloor$. In Lemma 6 the second argument of $b_1$ is the exponent of $n$
and the third is the shift of $p$.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Definition 5 (with `c, d, c₁, d₁` from Definition 4).
