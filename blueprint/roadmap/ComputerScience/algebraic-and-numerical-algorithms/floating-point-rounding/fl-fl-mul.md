# Innocuous double rounding of products

Let $K$ be a linearly ordered field with a floor
function and let $p \ge 1$ and $p' \ge 2p$ be natural numbers. For all binary floating-point numbers
$x, y \in K$ with $p$-bit significands and unbounded exponent, rounding $xy$ to nearest, ties to
even, first with $p'$ bits and then with $p$ bits gives the same as rounding it directly with $p$
bits: $\mathrm{fl}_p(\mathrm{fl}_{p'}(xy)) = \mathrm{fl}_p(xy)$.
