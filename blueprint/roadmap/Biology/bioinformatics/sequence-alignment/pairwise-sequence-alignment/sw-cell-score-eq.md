# The Smith–Waterman recurrence

Let $\sigma$ be a substitution score and $g$ a gap score,
and for a sequence $s$ and a letter $c$ write $sc$ for $s$ followed by $c$. For all sequences
$x$ and $y$ and all letters $a$ and $b$, the terminal Smith–Waterman cell $H$ satisfies

$$H(xa, yb) = \max\bigl(0,\ H(x, y) + \sigma(a, b),\ H(x, yb) + g,\ H(xa, y) + g\bigr).$$
