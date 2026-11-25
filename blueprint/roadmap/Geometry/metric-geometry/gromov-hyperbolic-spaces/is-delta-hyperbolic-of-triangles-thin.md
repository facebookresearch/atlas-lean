# Thin triangles imply hyperbolicity

If $X$ is a geodesic space whose geodesic triangles are all $\delta$-thin and $\delta \ge 0$, then $X$ is $\delta$-hyperbolic.

Given $w, x, y, z$, let $t_0 = \min((x \cdot y)_w, (y \cdot z)_w)$ and take the points at distance $t_0$ from $w$ on segments from $w$ to $x$, $y$ and $z$. Thinness of the triangles $wxy$ and $wyz$ puts the points on $[w, x]$ and $[w, z]$ within $2\delta$ of each other, and the triangle inequality through $x$ and $z$ then gives $(x \cdot z)_w \ge t_0 - \delta$.

This is stronger than the source: Gromov's Lemma 6.3.B and Proposition 6.3.C conclude $2\delta$-hyperbolicity, because the lower bound (**) in his proof, $|x_1' - x_2'| \ge 2(t - (x_1 \cdot x_2) - \delta)$, holds without the $-\delta$.

## Sources

- M. Gromov, *Hyperbolic groups*, in *Essays in Group Theory* (S. M. Gersten, ed.), Math. Sci. Res. Inst. Publ. 8, Springer, 1987, 75–263, Lemma 6.3.B and Proposition 6.3.C (constant $2\delta$).
