# The relative error bound

Let $K$ be a linearly ordered field with a floor function and
let $p$ be a natural number. For every $x \in K$, the rounding $\mathrm{fl}(x)$ of $x$ to
nearest, ties to even, with $p$-bit significands satisfies
$|\mathrm{fl}(x) - x| \le u\,|x|$, where $u = 2^{-p}$ is the unit roundoff.

The exponent is unbounded, so the bound holds for every $x$, with no underflow or overflow.
