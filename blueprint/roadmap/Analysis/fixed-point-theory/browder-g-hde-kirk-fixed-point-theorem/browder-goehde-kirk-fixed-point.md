# Browder–Göhde–Kirk fixed point theorem

Let $E$ be a uniformly convex real Banach space and
let $K \subseteq E$ be a nonempty, closed, bounded, convex set. If a map $f : E \to E$ sends $K$
into $K$ and is nonexpansive on $K$, that is, $\|f(x) - f(y)\| \le \|x - y\|$ for all
$x, y \in K$, then $f$ has a fixed point in $K$: there is $y \in K$ with $f(y) = y$.

## Sources

- F. E. Browder, *Nonexpansive nonlinear operators in a Banach space*, Proc. Nat. Acad. Sci. USA 54 (1965), 1041–1044.
- D. Göhde, *Zum Prinzip der kontraktiven Abbildung*, Math. Nachr. 30 (1965), 251–258.
- W. A. Kirk, *A fixed point theorem for mappings which do not increase distances*, Amer. Math. Monthly 72 (1965), 1004–1006.
- K. Goebel and W. A. Kirk, *Topics in Metric Fixed Point Theory*, Cambridge University Press, 1990. Lean states complete uniformly convex real case with `Bornology.IsBounded` convex set.
