# Sprague–Grundy value $5$ of P&R Helper on region $U$

Let $x \le y \le z$ be natural
numbers with $z < x + y$ and $y \le 2x + 1$ (the region $U$). The P&R Helper position $[x, y, z]$
is equivalent to the Nim heap $*5$, that is, has Sprague–Grundy value $5$, if and only if one of
the following holds:
- $[x, y, z]$ is $[3, 4, 4]$ or $[7, 8, 9]$;
- $y = x + 1$, $z = x + 3$, $x \equiv 0 \pmod 4$ and $x \notin \{0, 4, 8\}$;
- $y = x + 2$, $z = x + 3$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
- $y = x + 1$, $z = x + 5$ and $x \equiv 2 \pmod 8$;
- $y = x + 1$, $z = x + 6$ and $x \equiv 1 \pmod 8$;
- $y + z - x \equiv 7 \pmod 8$, $y = x + 2$, $z > x + 4$ and $x + y - z > 2$;
- $y + z - x \equiv 7 \pmod 8$, $z = x + y - 3$ and $x + 2 < y \le 2x$.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `5` on `U`.
