# Spherical law of cosines

Write $x \cdot y = \sum_{i=1}^{3} x_i y_i$ for the dot product
and $\lVert x \rVert = \sqrt{x \cdot x}$ for the Euclidean norm on $\mathbb{R}^3$. Let
$u, v, w \in \mathbb{R}^3$ be unit vectors and let $a, b, c, C$ be real numbers, each strictly
between $0$ and $\pi$. Suppose that $v \cdot w = \cos a$, $u \cdot w = \cos b$,
$u \cdot v = \cos c$ and

$$
\cos C = \frac{u \cdot v - (u \cdot w)(v \cdot w)}
{\lVert u - (u \cdot w)\, w \rVert \, \lVert v - (v \cdot w)\, w \rVert}.
$$

Then $\cos c = \cos a \cos b + \sin a \sin b \cos C$.

Geometrically, $u$, $v$, $w$ are the vertices of a spherical triangle on the unit sphere, $a$,
$b$, $c$ are the lengths of the sides opposite $u$, $v$, $w$, and $C$ is the angle at $w$,
opposite the side $c$.

## Sources

- https://en.wikipedia.org/wiki/Spherical_law_of_cosines (statement `spherical-cosines-s1`). It follows from `spherical_law_of_cosines_general`; the hypotheses `hc` and `hC` are unused and keep the source's shape. Proves `Wanted` entry `spherical_law_of_cosines`.
