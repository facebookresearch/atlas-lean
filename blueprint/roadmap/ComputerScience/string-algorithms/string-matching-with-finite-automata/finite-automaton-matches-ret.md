# Correctness of the finite-automaton matcher

For every pattern $P$ and text $T$ over the
alphabet $\{0, \dots, A-1\}$, the list of shifts returned by the finite-automaton matcher equals
the list returned by the naive string matcher.

So it is the complete increasing list of zero-based shifts at which $P$ occurs in $T$, including
overlapping occurrences and, for the empty pattern, every boundary.
