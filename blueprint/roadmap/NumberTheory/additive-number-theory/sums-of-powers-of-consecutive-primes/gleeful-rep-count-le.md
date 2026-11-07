# Upper bound for the number of gleeful representations

Let $p_1 = 2, p_2 = 3, \dots$ be
the primes in increasing order, and for natural numbers $k$ and $x$ let $s_k(x)$ be the number
of pairs $(n, m)$ of natural numbers with $m \ge 1$ and $p_{n+1}^k + \cdots + p_{n+m}^k \le x$.
Let $k > 1$, $M_0 \ge 6$ and $x$ be natural numbers with $p_1^k + \cdots + p_{M_0}^k \le x$. Put
$y = M_0$, let $\log$ be the natural logarithm, and set

$$A = \frac{\log(y/2)}{\log y},$$



$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1},$$



$$C = \Big(\frac{y}{y-1}\Big)^{1/(k+1)} B^{k/(k+1)}, \qquad E = 1 + \frac{1}{(k+1)A - 1},$$



$$F = \Big(\frac{y+1}{y}\Big)^{(k-1)/k} 4^{(k-1)/(k(k+1))} C^{(k-1)/k} E,$$

$U = 1.25506\,F$ and $c_k = \frac{k^2}{k-1} (k+1)^{(k-1)/k}$. Then

$$s_k(x) \le c_k \cdot \frac{x^{2/(k+1)}}{(\log x)^{2k/(k+1)}} \cdot U.$$

The paper prints the exponent of $\log x$ as $k/(k+1)$; its proof ends with $2k/(k+1)$, which
is stated here and implies the printed bound because $\log x \ge 1$.

## Sources

- Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84, Theorem 1 and its proof, with `c_k, A, B, C, E, F, U` from Section 2.
