# Successive gcd quotients

For a finite sequence $G = (g_1, \dots, g_k)$ of natural numbers,
let $d_i$ be the greatest common divisor of the first $i$ entries of $G$ (of all of $G$ when
$i > k$), with $d_0 = 0$. For $j \ge 1$ the successive gcd quotient is $c_j = d_{j-1} / d_j$,
taken to be $0$ when $d_j = 0$, that is, when the first $j$ entries are all zero; and $c_0 = 0$.

The source always assumes $g_1 > 0$ or $\gcd(G) = 1$, which avoids the degenerate case
$d_j = 0$. For example, $(660, 550, 352, 50, 201)$ has $(c_2, \dots, c_5) = (6, 5, 11, 2)$ and
$(3, 4, 5)$ has $(c_2, c_3) = (3, 1)$.

## Sources

- JIS statements `jis_0047f665dcff445f0a87ef54`, `jis_e21a41021ffe77e39d11f0e2`, `jis_480413725b64a0d49eabe98d`, `jis_ce7ca3b188a2135cbe5b0077`.
