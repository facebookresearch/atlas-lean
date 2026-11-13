# Fuel-bounded Smith–Waterman recursion

Fix a substitution score
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$, and write $ax$ for
the sequence with first element $a$ followed by $x$. For a fuel $n \in \mathbb{N}$ and sequences
$x, y$ over $\alpha$, the value $F_n(x, y) \in \mathbb{Z}$ is defined by $F_0(x, y) = 0$, by
$F_{n+1}(x, y) = 0$ if $x$ or $y$ is empty, and by

$$F_{n+1}(ax, by) = \max\bigl(0,\ F_n(x, y) + \sigma(a, b),\ F_n(x, by) + g,
\ F_n(ax, y) + g\bigr).$$

This is an exponential-time specification, not a memoized table.
