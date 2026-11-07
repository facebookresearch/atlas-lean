# Telescopic sequences

Let $G = (g_1, \dots, g_k)$ be a finite sequence of natural numbers.
For $0 \le i \le k$ let $d_i$ be the greatest common divisor of $g_1, \dots, g_i$, with $d_0 = 0$,
and for $1 \le j \le k$ let $c_j = d_{j-1} / d_j$ be the successive gcd quotient, taken to be $0$
when $d_j = 0$. The sequence $G$ is telescopic when $k \ge 2$, $g_1 + g_2 > 0$, and for every $j$
with $2 \le j \le k$ the number $c_j g_j$ lies in the additive submonoid of $\mathbb{N}$ generated
by $g_1, \dots, g_{j-1}$.

## Sources

- JIS statements `jis_480413725b64a0d49eabe98d`, `jis_5da42b058565b53729b9afa2`, `jis_a68226f2d394da5aef17cdad`, `jis_ce7ca3b188a2135cbe5b0077`, `jis_e21a41021ffe77e39d11f0e2`.
