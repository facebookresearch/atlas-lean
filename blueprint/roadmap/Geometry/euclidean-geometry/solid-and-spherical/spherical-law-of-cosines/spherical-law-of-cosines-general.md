# Spherical law of cosines, general form

Write $x \cdot y = \sum_{i=1}^{3} x_i y_i$ for the
dot product and $\lVert x \rVert = \sqrt{x \cdot x}$ for the Euclidean norm on $\mathbb{R}^3$. Let
$u, v, w \in \mathbb{R}^3$ be unit vectors and let $a, b, c, C$ be real numbers with $0 < a < \pi$
and $0 < b < \pi$. Suppose that $v \cdot w = \cos a$, $u \cdot w = \cos b$, $u \cdot v = \cos c$
and

$$
\cos C = \frac{u \cdot v - (u \cdot w)(v \cdot w)}
{\lVert u - (u \cdot w)\, w \rVert \, \lVert v - (v \cdot w)\, w \rVert}.
$$

Then $\cos c = \cos a \cos b + \sin a \sin b \cos C$.

Only $a$ and $b$ need to lie in $(0, \pi)$: $c$ and $C$ enter only through their cosines. The
quotient above is the cosine of the angle at $w$ between the great-circle arcs from $w$ to $u$
and from $w$ to $v$.
