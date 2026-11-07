# Weighted summation of Dirichlet convolutions

Let $u$ and $v$ be completely
multiplicative arithmetic functions with complex values, let $w$ be any arithmetic function with
complex values, let $*$ denote Dirichlet convolution, let $\mu$ be the Möbius function, put
$g = w * \mu$, and for real $y$ put $D(y) = \sum_{1 \le j \le y} (u * v)(j)$. Then for every
real $x$,

$$
\sum_{1 \le j \le x} w(j)\, (u * v)(j) =
\sum_{1 \le r \le x} g(r) \sum_{d \mid r} u(d)\, v(r/d) \sum_{m \mid d} \mu(m)\, v(m)\,
D\left(\frac{x}{mr}\right),
$$

where $r$, $d$ and $m$ run over positive integers.

Both sides vanish for $x < 1$; the source assumes $x \ge 1$.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Theorem 1, Equation (8) (`integers-2024-A75-thm-1`).
