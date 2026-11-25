# Determinant formula for the area of a triangle

For all points $a, b, c$ of the Euclidean plane $\mathbb{R}^2$, the area of the convex hull of
$\{a, b, c\}$ is $\frac{1}{2} \lvert (b_1 - a_1)(c_2 - a_2) - (b_2 - a_2)(c_1 - a_1) \rvert$.

## Idea

The triangle is the image of the standard triangle $\{(s, t) : s, t \ge 0,\ s + t \le 1\}$, of area
$\frac12$, under the affine map $(s, t) \mapsto a + s(b - a) + t(c - a)$, and Lebesgue measure scales
under an affine map by the absolute value of the determinant of its linear part, here
$(b_1 - a_1)(c_2 - a_2) - (b_2 - a_2)(c_1 - a_1)$. A triangle with collinear vertices has area $0$,
matching a zero determinant.

## Statements

- [Determinant formula for the area of a triangle](to-real-volume-convex-hull-triangle.md)
