# Varignon's theorem

Let $A$, $B$, $C$, $D$ be any four points of the Euclidean plane
$\mathbb{R}^2$, degenerate and self-crossing configurations included, and let $P$, $Q$, $R$,
$S$ be the midpoints of $AB$, $BC$, $CD$, $DA$, that is $2P = A + B$, $2Q = B + C$,
$2R = C + D$ and $2S = D + A$. Write $[XYZ]$ for the oriented area of the triangle $XYZ$,
positive when $X$, $Y$, $Z$ are listed counterclockwise. Then $P + R = Q + S$, so the diagonals
of $PQRS$ bisect each other and $PQRS$ is a possibly degenerate parallelogram, and

$$2([PQR] + [PRS]) = [ABC] + [ACD],$$

that is, the signed area of $PQRS$ is half the signed area of $ABCD$.

## Sources

- https://en.wikipedia.org/wiki/Varignon%27s_theorem. `A B C D` are arbitrary points in the Euclidean plane, including degenerate or self-crossing configurations. `P Q R S` are the midpoints of sides AB, BC, CD, DA (`2 • P = A + B`, etc.). Conclusion: `P + R = Q + S` (the diagonals of PQRS bisect each other, i.e. PQRS is a parallelogram via parallel opposite sides / bisecting diagonals), and twice the signed area of PQRS, expressed through `EuclideanGeometry.orientedTriangleArea`, equals the signed area of ABCD.
