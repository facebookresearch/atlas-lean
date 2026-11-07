# The terminal Smith–Waterman cell

Given a substitution score $\sigma(a, b) \in \mathbb{Z}$
for letters $a, b$ and a gap score $g \in \mathbb{Z}$, and writing $sc$ for a sequence $s$
followed by a letter $c$, the terminal Smith–Waterman cell $H(x, y)$ of two sequences $x$ and
$y$ is the integer defined by $H(x, y) = 0$ when $x$ or $y$ is empty, and

$$H(xa, yb) = \max\bigl(0,\ H(x, y) + \sigma(a, b),\ H(x, yb) + g,\ H(xa, y) + g\bigr)$$

for all sequences $x, y$ and letters $a, b$. It is the entry $H(|x|, |y|)$ of the
Smith–Waterman dynamic-programming table.

For $g \le 0$ it equals the maximum Needleman–Wunsch score over pairs of suffixes of $x$ and $y$;
for $g > 0$ it can be strictly smaller (for one-letter sequences with $\sigma = -100$ and
$g = 1$ the cell is $1$, while the alignment with two gap columns scores $2$). It is not the
optimal local alignment score over all positions; that is the Smith–Waterman score, the maximum
of this cell over all pairs of prefixes.
