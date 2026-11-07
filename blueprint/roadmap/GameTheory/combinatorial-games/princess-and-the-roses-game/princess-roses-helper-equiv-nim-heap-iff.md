# Sprague–Grundy values of P&R Helper on region R

Let $x \le y \le z$ be natural numbers
with $z < x + y$ and $y > 2x + 1$ (the region $R$), and write $s = y + z - x$. For every natural
number $n$, the P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $n$
(that is, has Sprague–Grundy value $n$) if and only if one of the following holds: $n = 0$ and
$x$, $y$, $z$ are all even; $n = 1$ and $s \equiv 1 \pmod 4$; $n = 2$, $x$ is even and $y$, $z$
are odd; $n = 3$ and $s \equiv 3 \pmod 4$; $n = 4$, $x$ is odd and $s \equiv 0 \pmod 4$;
$n = 5$, $x$ is odd and $s \equiv 2 \pmod 4$.

## Sources

- Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*, INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), region `R`.
