# Marden's theorem

Let $a, b, c$ be complex numbers such that $(b - a)/(c - a)$ has
nonzero imaginary part, so that they are the vertices of a nondegenerate triangle, and let
$p(z) = (z - a)(z - b)(z - c)$. Then there are complex numbers $f_1, f_2$ and a real number $L$
such that the roots of $p'$, counted with multiplicity, are exactly $f_1$ and $f_2$, and such
that the function $\sigma(z) = |z - f_1| + |z - f_2|$ satisfies
$\sigma((a + b)/2) = \sigma((b + c)/2) = \sigma((c + a)/2) = L$ and, for every real $t \ne 0$,
$\sigma((a + b)/2 + t(b - a)) > L$, $\sigma((b + c)/2 + t(c - b)) > L$ and
$\sigma((c + a)/2 + t(a - c)) > L$.

Thus the ellipse $\sigma(z) = L$ with foci $f_1$ and $f_2$ (a circle when $f_1 = f_2$) passes
through the midpoints of the three sides and touches each side line only at its midpoint: it is
the Steiner inellipse, and its foci are the roots of $p'$.

Proof: The statement is Marden's theorem (M. Marden, *Geometry of Polynomials*, 2nd ed.,
Math. Surveys No. 3, AMS, 1966; D. Kalman, *An Elementary Proof of Marden's Theorem*,
Amer. Math. Monthly 115(4) (2008), 330-338, <https://doi.org/10.1080/00029890.2008.11920532>).
Following [Wikipedia, *Marden's theorem*](https://en.wikipedia.org/wiki/Marden%27s_theorem),
we use Vieta's relations, the midpoint identity for the derivative, and the ellipse reflection
property expressed by a strict triangle inequality.

## Sources

- https://en.wikipedia.org/wiki/Marden%27s_theorem.
