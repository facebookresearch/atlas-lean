# Intersection points of two fans of rays

Let $m, n \ge 1$, $P = (-1, 0)$ and
$Q = (1, 0)$. From $P$ draw the $m$ closed rays at angles $\pi - 2\pi s/m$ for $0 \le s < m$, and
from $Q$ the $n$ closed rays at angles $2\pi t/n$ for $0 \le t < n$. Let
$h = \lfloor (m - 1)/2 \rfloor$. Then the number of points that are $P$, $Q$, or a point off the
$x$-axis lying on a ray from $P$ and on a ray from $Q$ is
$2 \sum_{s=1}^{h} \lceil ns/m - 1/2 \rceil + 2$ for odd $n$ and
$2 \sum_{s=1}^{h} \lceil ns/m \rceil - 2h + 2$ for even $n$.

Off the $x$-axis these are exactly the points where two rays meet; on the axis, rays meet only at
$P$, $Q$ or along overlapping segments, which the paper does not count.

## Sources

- Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29 (2026), Article 26.1.8, Theorem 16 (`jis-2026-26.1.8-thm-16`).
