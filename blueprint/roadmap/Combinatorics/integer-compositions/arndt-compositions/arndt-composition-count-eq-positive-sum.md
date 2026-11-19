# Positive sum for Arndt compositions

Let $a(n, m)$ be the number of Arndt compositions of
$n$ with $m$ parts, and write $h = \lfloor m/2 \rfloor$. For all $n \ge 0$ and $m \ge 1$: if
$m + h \le n$, then

$$a(n, m) = \sum_{\ell=0}^{\lfloor (n-m-h)/2 \rfloor} \binom{h+\ell-1}{\ell}
\binom{n-2h-2\ell-1}{\lfloor (m-1)/2 \rfloor},$$

and otherwise $a(n, m) = 0$. Here $\binom{-1}{0} = 1$ (this term occurs for $m = 1$).

The paper states it for all $n, m \ge 0$; at $n = m = 0$ it fails ($a(0, 0) = 1$, while the only
term has lower index $\lfloor -1/2 \rfloor = -1$ and vanishes), so the case $m = 0$ is omitted.

## Sources

- Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions Approach*, INTEGERS 24 (2024), Article A35, Theorem 3.
