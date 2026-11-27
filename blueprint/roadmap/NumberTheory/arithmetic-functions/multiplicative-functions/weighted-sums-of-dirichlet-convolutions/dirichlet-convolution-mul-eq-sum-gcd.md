# Gcd expansion of a convolution of completely multiplicative functions at a product

Let
$u$ and $v$ be complex-valued completely multiplicative arithmetic functions, meaning
$u(mn) = u(m) u(n)$ and $v(mn) = v(m) v(n)$ for all natural numbers $m$ and $n$. Let $u * v$ be
their Dirichlet convolution and $\mu$ the Möbius function. Then for all natural numbers $r$ and
$s$,

$$(u * v)(rs) = \sum_{m \mid \gcd(r, s)} \mu(m) u(m) v(m) (u * v)(r/m) (u * v)(s/m),$$

the sum running over the positive divisors $m$ of $\gcd(r, s)$ (it is empty when $r = s = 0$).

The paper takes $r, s$ positive; the identity also holds (both sides vanish) when $r$ or $s$
is $0$, so no positivity hypothesis is imposed.

## Sources

- André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75, Lemma 2, Equation (17).
