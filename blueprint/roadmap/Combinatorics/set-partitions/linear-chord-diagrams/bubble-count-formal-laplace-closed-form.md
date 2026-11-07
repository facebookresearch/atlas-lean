# Closed form of the bubble generating function

In $\mathbb{Q}[[t, w, y]]$ let
$D = 1 - w(1 - wy)$ and let $I(t, w, y)$ be the power series

$$I = \frac{(1-w)^2 (1-wy)^2}{(1+w^2y)\,D^2}
\exp\!\left(\frac{y}{2}\left(\frac{tw}{1+w^2y}\right)^2\right) +
\left(\frac{(2 - w(y+2)(1 + y(1 - w(2-wy))))\,wy}{D^2} + \frac{(1-wy)\,t^2 w y^3}{D}\right)
\exp\!\left(\frac{t^2 y}{2}\right),$$

and write $[t^m w^p y^n]\,I$ for its coefficient of $t^m w^p y^n$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n \ge 1$ and $p \ge 0$

$$\sum_{m \ge 0} m!\, [t^m w^p y^n]\,I = B_{n,p}.$$

The sum has only finitely many nonzero terms, since $t$ occurs in $I$ only as $t^2$ times a
factor $y$. Replacing $t^m$ by $m! = \int_0^\infty t^m e^{-t}\,dt$ reads the formula as a formal
Laplace transform in $t$, as in the paper's proofs of Lemmas 3 and 4, so that the left side is
the coefficient of $y^n w^p$ of the paper's $B(y, w) = \sum_{n,p} B_{n,p} y^n w^p$. The case
$n = 0$ is excluded: the printed formula has constant term $1$ while $B_{0,0} = 0$ (the paper's
residue computation in its contour variable $x$ omits the residue $-1$ at $x = 0$; Theorem 1
gives constant term $0$).

## Sources

- Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer Sequences 27 (2024), Article 24.4.2, Corollary 2 (`jis-2024-24.4.2-cor-2`).
