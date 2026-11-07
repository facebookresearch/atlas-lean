# Finite-automaton string matcher

Let $P$ be a pattern of length $m$ and $T$ a text over
the alphabet $\{0, \dots, A-1\}$. This timed computation first computes the transition table of
$P$, then runs through $T$ starting in state $0$: on reading the $i$-th symbol $a$ of $T$ in
state $q$ it moves to the state given by the table entry at index $qA + a$, and if that state is
$m$ it reports the shift $i - m$. If $m = 0$, the shift $0$ is also reported before the scan.
It returns the reported shifts in the order found. The cost is that of computing the table,
plus two units for each symbol of $T$ (a table lookup and an acceptance test), plus one unit for
each reported shift.

The table is computed once, before the single pass over the text, and the scan does not reset
after a match, so overlapping occurrences are reported.
