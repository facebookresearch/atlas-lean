# Lower bound for the number of gleeful representations

Let $p_1 = 2, p_2 = 3, \dots$ be
the primes in increasing order, and for natural numbers $k$ and $x$ let $s_k(x)$ be the number
of pairs $(n, m)$ of natural numbers with $m \ge 1$ and $p_{n+1}^k + \cdots + p_{n+m}^k \le x$.
Let $k > 1$, $M_0 \ge 6$ and $x$ be natural numbers with $p_1^k + \cdots + p_{M_0}^k \le x$. Put
$y = M_0$, let $\log$ be the natural logarithm, and set

$$D = \frac{y}{y+3} \Big(\frac{\log(y/2)}{\log y + 2 \log\log(y+2)}\Big)^{k/(k+1)}$$

and $L = \frac{y-1}{y} D^2$. Then

$$\frac{(k+1)^2}{2} \cdot \frac{x^{2/(k+1)}}{(\log x)^{2k/(k+1)}} \cdot L \le s_k(x).$$

The paper prints the exponent of $\log x$ as $k/(k+1)$; its proof gives $2k/(k+1)$, which is
stated here. The printed form contradicts the upper bound for $s_k(x)$ for large $x$.

## Sources

- Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84, Theorem 2 and its proof, with `D`, `L` from Section 2.
