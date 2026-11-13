# The local score equals the Smith–Waterman score

Let $\sigma$ be an integer-valued
substitution score on letters and let $g$ be an integer gap score with $g \le 0$. Then for all
sequences $x$ and $y$, the local score of $x$ and $y$ (the maximum Needleman–Wunsch score over
pairs of infixes) equals their Smith–Waterman score (the maximum terminal-cell score over pairs
of prefixes).

The proof uses that an infix is a suffix of a prefix and that the terminal cell is a maximum
over pairs of suffixes.
