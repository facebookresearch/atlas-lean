# P&R Helper positions of Sprague–Grundy value 3 on region U

For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $3$ (that is, has
Sprague–Grundy value $3$) if and only if one of the following holds:
(a) $(x, y, z)$ is one of $(1, 2, 2)$, $(2, 2, 3)$, $(5, 6, 6)$, $(6, 6, 7)$, $(3, 4, 5)$,
$(5, 5, 8)$;
(b) $y = x$, $z = x + 1$, $x \equiv 0 \pmod 4$ and $x \notin \{0, 4\}$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
(d) $y = x + 1$, $z = x + 2$, $x \equiv 1 \pmod 4$ and $x \notin \{1, 5\}$;
(e) $s \equiv 0 \pmod 8$, $y = x$, $x$ is odd and $z > x + 5$;
(f) $s \equiv 6 \pmod 8$, $x$, $y$, $z$ are not all even, and either $z > x + 4$ and
$y \le x + 1$, or $z > x + 2$ and $z = x + y - 2$;
(g) $s \equiv 3 \pmod 4$, $z > x + 2$, it is not the case that $s \equiv 7 \pmod 8$,
$z > x + 4$ and $y \le x + 2$, and it is not the case that $s \equiv 7 \pmod 8$, $y \le 2x$
and $x + y - z \le 3$.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Theorem 13, value `3` on `U`.
