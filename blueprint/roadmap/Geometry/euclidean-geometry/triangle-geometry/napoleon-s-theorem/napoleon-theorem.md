# Napoleon's theorem

Let $A$, $B$, $C$ be pairwise distinct, non-collinear points of the
Euclidean plane $\mathbb{R}^2$, and let $A_2$, $B_2$, $C_2$ be points with
$|BA_2| = |CA_2| = |BC|$, $|CB_2| = |AB_2| = |CA|$ and $|AC_2| = |BC_2| = |AB|$, such that $A_2$
and $A$ lie strictly on opposite sides of the line $BC$, $B_2$ and $B$ lie strictly on opposite
sides of the line $CA$, and $C_2$ and $C$ lie strictly on opposite sides of the line $AB$. Let
$G_1 = \frac{1}{3}(B + C + A_2)$, $G_2 = \frac{1}{3}(C + A + B_2)$ and
$G_3 = \frac{1}{3}(A + B + C_2)$. Then $|G_1G_2| = |G_2G_3| = |G_3G_1|$.

That is, the centroids of the equilateral triangles erected outward on the sides of $ABC$ are
pairwise equidistant. Non-collinearity is stated as $(B - A) \times (C - A) \ne 0$ and opposite
sides by signed areas, for instance $((C - B) \times (A - B)) \, ((C - B) \times (A_2 - B)) < 0$,
where $(x, y) \times (x', y') = x y' - y x'$.

## Sources

- https://en.wikipedia.org/wiki/Napoleon%27s_theorem (statement id `napoleon-s1`; raw: "Outer equilateral-triangle centers on any triangle form an equilateral triangle."). It follows from `napoleon_theorem_general`, which also shows the common distance is positive; the hypotheses `A ≠ B`, `B ≠ C`, `C ≠ A` and nondegeneracy are unused and keep the source's shape. Proves `Wanted` entry `napoleon_theorem`.
