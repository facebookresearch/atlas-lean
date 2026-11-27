# Campbell's interpolation

Let $h_2$ be Campbell's sequence and $h_3^{(m)}$ the auxiliary
piecewise-linear functions of the construction, and for $n \ge 1$ put $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$. Campbell's interpolation is the function $f : \mathbb{R} \to \mathbb{R}$
with $f(x) = \frac{89}{110} e^{(100/89)(11x - 100)} + \frac{1}{10}$ for $x \le 100/11$ and
$f(x) = 10x - 90$ for $100/11 < x \le 10$. For $x > 10$ put
$m = \lfloor \log_{10} \lfloor x \rfloor \rfloor + 1$, so that $m \ge 2$ and
$10^{m-1} \le x < 10^m$; then

$$
f(x) = \frac{x (y_2(m) - y_1(m)) - (y_1(m) + 10^{m-1} y_2(m) - 10^m y_1(m))}{9 \cdot 10^{m-1} - 1}
$$

if $x \le 10^m - 1$, and $f(x) = h_2(10^m - 1) + \int_{10^m - 1}^{x} h_3^{(m)}(t) \, dt$ if
$x > 10^m - 1$.

The paper defines $f$ on $[0, \infty)$ only; here the first formula is used for every
$x \le 100/11$. At a power of ten $x = 10^{m-1} > 10$ the formula for index $m$ is used; the piece
to its left takes the same value there.

## Sources

- John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (15) and (21).
