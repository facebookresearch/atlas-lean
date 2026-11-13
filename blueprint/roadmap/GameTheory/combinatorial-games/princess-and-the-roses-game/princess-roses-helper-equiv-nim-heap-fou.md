# P&R Helper positions of Sprague–Grundy value 4 on region U

For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $4$ (that is, has
Sprague–Grundy value $4$) if and only if one of the following holds:
(a) $(x, y, z)$ is one of $(2, 3, 3)$, $(5, 6, 7)$, $(4, 4, 5)$, $(7, 8, 8)$;
(b) $y = x$, $z = x + 1$, $x \equiv 2 \pmod 4$ and $x \notin \{2, 6\}$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 1 \pmod 4$ and $x \notin \{1, 5\}$;
(d) $y = x + 1$, $z = x + 2$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
(e) $y = x + 1$, $z = x + 5$ and $x \equiv 1 \pmod 8$;
(f) $s \equiv 0 \pmod 4$, $x$, $y$, $z$ are not all even, $z > x + 2$, and none of the
following holds: $(x, y, z) = (5, 5, 8)$; $z > x + 4$, $s \equiv 4 \pmod 8$ and $y = x$;
$z > x + 5$, $s \equiv 0 \pmod 8$ and $y = x$; $y = x + 1$, $z = x + 3$, $x \equiv 0 \pmod 4$
and $x \notin \{0, 4, 8\}$; $y = x + 2$, $z = x + 3$, $x \equiv 3 \pmod 4$ and
$x \notin \{3, 7\}$; $y = x + 1$, $z = x + 5$ and $x \equiv 2 \pmod 8$; $y = x + 2$,
$z = x + 5$ and $x \equiv 1 \pmod 8$; $y = x + 1$, $z = x + 6$ and $x \equiv 1 \pmod 8$.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Theorem 13, value `4` on `U`.
