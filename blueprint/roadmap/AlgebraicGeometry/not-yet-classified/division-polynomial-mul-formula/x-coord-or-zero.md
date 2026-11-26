# X-coordinate or zero

For a point $P$ of a Weierstrass curve over a field $F$, the element
of $F$ that is $x$ when $P = (x, y)$ is affine and $0$ when $P$ is the point at infinity. Unlike
Mathlib's projective `Point.xRep`, it is a single element of $F$, as in the source's
multiplication-formula predicate.
