# Double rounding is innocuous away from midpoints

Let $K$ be a linearly ordered field with
a floor function, let $p \ge 1$ and $d \ge 1$ be natural numbers, let $z \in K$, and let
$M = z / 2^e$, where $e$ is the exponent of the last place of $z$ at precision $p$. If $M$ is a
half-integer, or $|M - k| < 1/2 - 2^{-d-1}$ for some integer $k$, then rounding $z$ to nearest,
ties to even, first with $p + d$ bits and then with $p$ bits gives the same as rounding it directly
with $p$ bits: $\mathrm{fl}_p(\mathrm{fl}_{p+d}(z)) = \mathrm{fl}_p(z)$.

In other words, double rounding can differ from direct rounding only when $z$ is not a midpoint of
consecutive $p$-bit floating-point numbers but lies within half a last place of $p + d$ bits of
one.
