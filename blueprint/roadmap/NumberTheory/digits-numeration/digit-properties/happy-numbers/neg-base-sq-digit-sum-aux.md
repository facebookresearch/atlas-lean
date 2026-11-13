# Truncated digit-square sum in a negative base

For an integer $b$, define $T_b(f, a)$ for a
natural number $f$ and an integer $a$ by recursion on $f$: $T_b(0, a) = 0$, $T_b(f + 1, 0) = 0$,
and for $a \ne 0$, $T_b(f + 1, a) = r^2 + T_b(f, (a - r)/b)$, where $r = a \bmod b$ is the
remainder of $a$ on division by $b$, with $0 \le r < |b|$ (for $b = 0$ one takes $r = a$ and
$(a - r)/b = 0$). For $b \le -2$, $T_b(f, a)$ is thus the sum of the squares of the first $f$
base-$b$ digits of $a$, counted from the least significant one.

## Sources

- Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2.
