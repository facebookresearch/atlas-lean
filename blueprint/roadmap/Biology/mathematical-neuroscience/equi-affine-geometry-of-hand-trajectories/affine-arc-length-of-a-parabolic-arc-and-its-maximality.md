# Affine arc length of a parabolic arc and its maximality

Let $p_1, p_2 \in \mathbb{R}^2$ be the endpoints of a short convex arc $\Gamma$ whose tangent lines at $p_1$ and $p_2$ meet at $p_0$, and let $A = A(p_1, p_2)$ be the area of the **support triangle** $\Delta(p_1, p_0, p_2)$. The equi-affine arc length of $\Gamma$ is $\sigma(\Gamma) = \int_\Gamma \kappa^{1/3} ds$, and the **affine distance** of the pair of line elements $(p_1, p_1p_0)$, $(p_2, p_0p_2)$ is defined as

$$d(p_1, p_2) = 2\, A(p_1, p_2)^{1/3}.$$

**Theorem (Blaschke; Theorems 2 and 3 and the Lemma of Sect. 5.1 of the source).**

1. If $\Gamma$ is the parabolic arc with this support triangle, then $\sigma(\Gamma) = 2 A^{1/3} = d(p_1, p_2)$.
2. (Affine anti-triangle inequality.) If $p$ is an interior point of $\Gamma$, so that the subarcs $(p_1, p)$ and $(p, p_2)$ have support triangles cut out by the tangent at $p$, then $d(p_1, p) + d(p, p_2) \le d(p_1, p_2)$, with equality for the parabola.
3. Consequently, among all short arcs interpolating the two line elements, the parabolic arc maximizes the equi-affine arc length: $\sigma(\Gamma) \le 2 A^{1/3}$.

Parabolas are the plane curves of zero affine curvature and are the equi-affine geodesics (Theorem 1 of the source, after Griffiths 1983).

## Expansion

Part 1 can be checked on the quadratic Bezier parametrization $B(u) = (1-u)^2 p_1 + 2u(1-u) p_0 + u^2 p_2$, $u \in [0, 1]$, which traces the parabolic arc. With $a = p_0 - p_1$ and $b = p_2 - p_0$ one finds $B' = 2[(1-u) a + u b]$ and $B'' = 2(b - a)$, so $\det(B', B'') = 4 \det(a, b) = \pm 8A$ for every $u$, and $\sigma = \int_0^1 |\det(B', B'')|^{1/3} du = (8A)^{1/3}$. The equality case of part 2 is the de Casteljau subdivision of the Bezier curve, which makes the affine distance additive along a parabola; refining a partition of a general arc makes the sum of affine distances non-increasing and convergent to the affine arc length, which gives part 3. For the triangle with vertices $(0,0)$, $(0, 1/2)$, $(1/2, 0)$ the parabolic arc has $\sigma = 1$, while the quarter circle of radius $1/2$ with the same support triangle has $\sigma = 2^{1/3} \pi / 4 \approx 0.99$. In the motor-control interpretation, a stroke between two prescribed positions and directions is modeled by the interpolating parabola, executed at [constant equi-affine speed](one-third-power-law-as-constant-equi-affine-speed.md).

## Depends on

- [The one-third power law is motion at constant equi-affine speed](one-third-power-law-as-constant-equi-affine-speed.md)

## Sources

- T. Flash and A. A. Handzel, *Affine differential geometry analysis of human arm movements*, Biological Cybernetics 96(6) (2007), 577-601. DOI: <https://doi.org/10.1007/s00422-007-0145-5>. PMCID: PMC2799626.
- W. Blaschke, *Vorlesungen über Differentialgeometrie II: Affine Differentialgeometrie*, Springer, Berlin (1923).
