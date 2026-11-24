# Homogeneous coordinates and perspective projection

Points $(x, y, z) \in \mathbb{R}^3$ correspond to the homogeneous coordinates $[x : y : z : 1]$ in real projective 3-space, and every invertible $4 \times 4$ matrix acts as a projective transformation. The pinhole perspective projection with focal length $f > 0$, $(x, y, z) \mapsto (f x/z, f y/z)$ for $z > 0$, maps every segment lying in the half-space $z > 0$ onto a segment of the image plane; it preserves collinearity and incidence but in general not ratios of lengths along a line (it preserves cross-ratios).

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- R. Hartley and A. Zisserman, *Multiple View Geometry in Computer Vision*, 2nd ed., Cambridge University Press, 2004
