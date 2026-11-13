# P&R Helper positions of Sprague–Grundy value 2 on region U

For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $2$ (that is, has
Sprague–Grundy value $2$) if and only if one of the following holds:
(a) $y = x$, $z = x$, $x \equiv 1 \pmod 4$ and $x \ne 1$;
(b) $y = x$, $z = x + 1$ and $x \equiv 3 \pmod 4$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 2 \pmod 4$ and $x \ne 2$;
(d) $y = x$, $z = x + 2$, $x \equiv 1 \pmod 4$ and $x \ne 1$;
(e) $y = x + 1$, $z = x + 2$, $x \equiv 0 \pmod 4$ and $x \ne 0$;
(f) $y = x + 2$, $z = x + 2$ and $x \equiv 3 \pmod 4$;
(g) $s \equiv 7 \pmod 8$, and either $z > x + 4$ and $y = x$, or $z > x + 5$ and $y = x + 1$,
or $z > x + 2$ and $z = x + y - 1$;
(h) $s \equiv 4 \pmod 8$, $y = x$, $x$ is odd and $z > x + 4$;
(i) $s \equiv 2 \pmod 4$, $x$, $y$, $z$ are not all even, $z > x + 2$, it is not the case that
$s \equiv 6 \pmod 8$, $z > x + 4$ and $y \le x + 1$, and it is not the case that
$s \equiv 6 \pmod 8$ and $z = x + y - 2$.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Theorem 13, value `2` on `U`.
