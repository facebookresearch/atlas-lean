# The Smith–Waterman score

Given a substitution score $\sigma$ and a gap score $g$, the
Smith–Waterman score of two sequences $x$ and $y$ is the maximum of the terminal Smith–Waterman
cell $H(p, q)$ over all pairs of a prefix $p$ of $x$ and a prefix $q$ of $y$ (the empty prefixes
included).

For $g \le 0$ this is the optimal local alignment score, the maximum Needleman–Wunsch score over
pairs of infixes; for $g > 0$ it can be smaller.
