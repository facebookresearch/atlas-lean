# Needleman–Wunsch score of two single letters

For every substitution score $\sigma$
assigning an integer to each pair of letters, integer gap score $g$ and letters $a$, $b$, the
Needleman–Wunsch score of the one-letter sequences $[a]$ and $[b]$ is
$\max(\sigma(a, b), g + g)$: the better of matching $a$ with $b$ and gapping both.
