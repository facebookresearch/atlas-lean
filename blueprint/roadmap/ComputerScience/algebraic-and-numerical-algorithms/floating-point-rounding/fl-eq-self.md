# Floating-point numbers round to themselves

Let $p \ge 1$ and let $x$ be an element of a
linearly ordered field with a floor function. If $x$ is a binary floating-point number with a
$p$-bit significand, that is, $x = m \cdot 2^e$ for some integers $m$ and $e$ with $|m| < 2^p$,
then rounding $x$ to nearest, ties to even, at precision $p$ returns $x$: $\mathrm{fl}_p(x) = x$.
