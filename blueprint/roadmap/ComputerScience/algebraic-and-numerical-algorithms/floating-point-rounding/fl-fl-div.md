# Innocuous double rounding of quotients

Let $K$ be a linearly ordered field with a floor
function and let $p \ge 1$ and $p' \ge 2p$ be natural numbers. For all binary floating-point numbers
$x, y \in K$ with $p$-bit significands and unbounded exponent, rounding $x / y$ to nearest, ties to
even, first with $p'$ bits and then with $p$ bits gives the same as rounding it directly with $p$
bits: $\mathrm{fl}_p(\mathrm{fl}_{p'}(x / y)) = \mathrm{fl}_p(x / y)$.

For $y = 0$ both sides are $0$, with the convention $x / 0 = 0$.
