# Position of the largest entry in permutations avoiding 321 and vincular 2143

For natural numbers $n, k$, let $a(n, k)$ be the number of permutations $\sigma$ of $\{0, \dots, n-1\}$ that avoid the classical pattern $321$, avoid the vincular pattern $2143$ (positions $i, i+1, j, k$ with $i + 1 < j < k$ and $\sigma(i+1) < \sigma(i) < \sigma(k) < \sigma(j)$), and take the largest value $n - 1$ at a position $j$ with $j + 1 = k$ (in $1$-based terms, $\sigma(k) = n$); in particular $a(n, 0) = 0$, since no position $j$ satisfies $j + 1 = 0$. Then:

- $a(n, 1) = 1$ for every $n \ge 1$;
- $a(n, n) = F_{2n-3}$ for every $n > 1$;
- $a(n, k) = a(n-1, k-1) + a(n-1, k)$ for $1 < k < n$;
- with $g(x, t) = \sum_{n \ge 0} \Big( \sum_{k=1}^{n} a(n, k)\, t^k \Big) x^n$, a power series in $x$ over $\mathbb{Q}[t]$,

    $$(1 - x - t x)(1 - 3 t x + t^2 x^2)\, g(x, t) = t x (1 - t x)(1 - 2 t x).$$

$F_m$ is the Fibonacci number with $F_0 = 0$, $F_1 = 1$, and the subtraction in the index is natural-number subtraction.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", *INTEGERS* 25 (2025), Article A79, Proposition 5.
