# Transition table of the string-matching automaton

Let $P$ be a pattern of length $m$
over the alphabet $\{0, \dots, A-1\}$ and write $P_k$ for its prefix of length $k$. This timed
computation returns a table of $(m+1)A$ entries in $\{0, \dots, m\}$, stored row by row: for
each state $q \le m$ and symbol $a < A$, the entry at index $qA + a$ is found by trying
$k = \min(m, q+1)$ and then each smaller value in turn, and is the first $k$ for which $P_k$ is
a suffix of the word $P_q a$ (the candidate $k = 0$ is always accepted). The cost counts
one unit for each candidate $k$ tried, one for each symbol comparison executed when comparing
$P_k$ with the last $k$ symbols of $P_q a$ (left to right, stopping at the first mismatch), one
for each move to a smaller candidate, and one for each table entry written.

## Sources

- CLRS fourth edition section 32.3, decreasing-candidate row-major construction.
