# Divisibility of the polynomial parts by $k(n-k)/2$

Let $m$ be a natural number and $n$ an
integer. For an integer $x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$,
and for a rational number $x$ write $(x)_r = x(x-1)\cdots(x-r+1)$ for the falling factorial. Then
there is a polynomial $Q \in \mathbb{Q}[X]$ such that for every natural number $k$

$$\binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1 = \frac{k(n-k)}{2} \, Q(k),$$

and for all natural numbers $i$ and $j$ with $1 \le i < j$ there is a polynomial
$Q \in \mathbb{Q}[X]$ such that for every natural number $k$

$$\frac{(n-k)_{j-i} \, (k)_i + (n-k)_i \, (k)_{j-i}}{j!} \binom{m-n}{\max(m-j, 0)} =
\frac{k(n-k)}{2} \, Q(k).$$

For $j \le m$ the left-hand sides are the polynomial parts of the coefficients
$C'_{00}(m, n, k)$ and $C'_{ji}(m, n, k)$ of Theorem 4 (the halving at $j = 2i$ does not affect
divisibility); agreement at every natural number $k$ amounts to divisibility by $k(n-k)/2$
in $\mathbb{Q}[k]$.

## Sources

- Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 1 (`integers-2026-A32-prop-1`).
