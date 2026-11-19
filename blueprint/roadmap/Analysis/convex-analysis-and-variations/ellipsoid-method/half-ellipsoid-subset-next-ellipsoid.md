# The central-cut ellipsoid contains the half-ellipsoid

For $n \ge 2$, a positive definite $A$, a centre $a$ and $c \ne 0$,

$$
E(a, A) \cap \{x : c^\top x \le c^\top a\} \subseteq E(a', A'),
$$

where $a'$ and $A'$ are the [centre](next-center.md) and [matrix](next-matrix.md) after the central-cut step. Goemans verifies it for the unit ball and the cut $x_1 \ge 0$, and reduces the general case by an affine change of variables. The proof here works directly with the [inverse of $A'$](next-matrix-inv.md): for $x$ in the half-ellipsoid put $y = x - a$, $q = y^\top A^{-1} y \le 1$ and $t = c^\top y / \sqrt{c^\top A c}$, so that $t \le 0$ and, by the Cauchy–Schwarz inequality for $A^{-1}$, $t^2 \le q$. Then

$$
(x - a')^\top A'^{-1} (x - a') = \frac{n^2 - 1}{n^2} \Bigl( q + \frac{2}{n-1}\, t (t + 1) + \frac{1}{n^2 - 1} \Bigr) \le \frac{n^2 - 1}{n^2} \Bigl( 1 + \frac{1}{n^2 - 1} \Bigr) = 1 ,
$$

because $-1 \le t \le 0$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, the computation before the proof of Lemma 7.1 and equations (4)-(5).
