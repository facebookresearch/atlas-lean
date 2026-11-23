# A face of a polytope is the convex hull of the vertices it contains

Let $s$ be a finite set of points and $F$ a face of $P = \operatorname{conv} s$. Then

$$F = \operatorname{conv}(F \cap s).$$

In particular every face of a polytope is again a polytope, spanned by some of the given points.

The proof writes a point $x \in F$ as a convex combination $x = \sum_{y \in s} w_y\, y$. If $\ell$
is a functional exposing $F$ with maximum $M = \ell(x)$, then
$\sum_y w_y (M - \ell(y)) = 0$ with every term nonnegative, so every $y$ with $w_y > 0$ satisfies
$\ell(y) = M$, that is, lies in $F$.

## Sources

- G. M. Ziegler, *Lectures on Polytopes*, Graduate Texts in Mathematics 152, Springer (cited for terminology only, without theorem numbers; not consulted for this entry).
