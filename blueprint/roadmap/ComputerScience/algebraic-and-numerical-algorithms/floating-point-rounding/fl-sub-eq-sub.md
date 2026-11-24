# Floating-point subtraction is exact under Sterbenz's condition

Let $p \ge 1$ and let $x$
and $y$ be binary floating-point numbers with $p$-bit significands in a linearly ordered field
with a floor function. If $y / 2 \le x \le 2y$, then rounding $x - y$ to nearest, ties to even,
at precision $p$ returns it exactly: $\mathrm{fl}_p(x - y) = x - y$.
