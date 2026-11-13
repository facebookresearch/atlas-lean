# Fuel-bounded Needleman–Wunsch recursion

Fix a substitution score
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$, and write $|x|$ for
the length of a sequence $x$ and $ax$ for the sequence with first element $a$ followed by $x$.
For a fuel $n \in \mathbb{N}$ and sequences $x, y$ over $\alpha$, the value
$N_n(x, y) \in \mathbb{Z}$ is defined by $N_0(x, y) = 0$, by $N_{n+1}(x, y) = g\,|y|$ if $x$ is
empty and $N_{n+1}(x, y) = g\,|x|$ if $y$ is empty, and by

$$N_{n+1}(ax, by) = \max\bigl(N_n(x, y) + \sigma(a, b),\ N_n(x, by) + g,\ N_n(ax, y) + g\bigr).$$

The Needleman–Wunsch score of $x$ and $y$ is $N_{|x|+|y|}(x, y)$; this fuel suffices because every
recursive call shortens the pair. This is an exponential-time specification, not a memoized
table.
