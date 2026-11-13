# Formal contour-integral formula for bubble counts

Let $G(s, w, y)$ be the power series
in $\mathbb{Q}[[s, w, y]]$ given by

$$G = \left(1 - \frac{y^2}{1 - sy + y^2}\right)^{-2} \left(\frac{1}{1 - wsy + w^2y^2} - 1\right),$$

and write $[s^a w^p y^m]\,G$ for its coefficient of $s^a w^p y^m$. For integers $n, p \ge 0$ let
$B_{n,p}$ be the total number of bubbles of size $p$ in all linear chord diagrams on $2n$
vertices. Then for all integers $n, p \ge 0$ (including $n = 0$)

$$\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n}]\,G = B_{n,p} \quad\text{and}\quad
\sum_{k \ge 0} \frac{(2k)!}{2^k\, k!}\, [s^{2k} w^p y^{2n+1}]\,G = 0.$$

Each sum has only finitely many nonzero terms, since every power of $s$ in $G$ comes with at
least the same power of $y$. This is the termwise reading of the paper's formal contour
integral: integrating $x^{-1} e^{x^2/2} G(t/x, w, y)$ over $x$ and then replacing $t^{2k}$ by
$\int_0^\infty t^{2k} e^{-t}\,dt = (2k)!$ turns $s^{2k}$ into $(2k)!/(2^k k!)$. The literal
integrals diverge.

## Sources

- Donovan Young, *Counting Bubbles in Linear Chord Diagrams*, Journal of Integer Sequences 27 (2024), Article 24.4.2, Theorem 1 (`jis-2024-24.4.2-thm-1`).
