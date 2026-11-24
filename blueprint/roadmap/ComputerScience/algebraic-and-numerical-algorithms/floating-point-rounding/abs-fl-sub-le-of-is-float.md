# Round to nearest for floating-point numbers

Let $K$ be a linearly ordered field with a
floor function and let $p \ge 1$. For every $x \in K$ and every binary floating-point number
$f \in K$ with a $p$-bit significand (and unbounded exponent), the rounding $\mathrm{fl}(x)$ of
$x$ to nearest, ties to even, with $p$-bit significands satisfies
$|\mathrm{fl}(x) - x| \le |f - x|$: no floating-point number is closer to $x$ than
$\mathrm{fl}(x)$.
