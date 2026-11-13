# Round to nearest, ties to even

For a natural number $p$ and an element $x$ of a linearly
ordered field with a floor function, let $e$ be the exponent of the last place of $x$ at precision
$p$, and let $\operatorname{rne}$ round to the nearest integer with ties to the even one. The
rounding of $x$ to nearest, ties to even, is
$\mathrm{fl}_p(x) = \operatorname{rne}(x / 2^e) \cdot 2^e$: scale $x$ so that its last place is the
units digit, round to the nearest integer with ties to even, and scale back.
