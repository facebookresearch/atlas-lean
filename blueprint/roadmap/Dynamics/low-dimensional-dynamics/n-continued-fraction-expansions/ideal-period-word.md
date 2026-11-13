# Ideal period words

For $n \ge 1$, the ideal period word $d_n$ is a finite list of blocks
of partial quotients, each block being $a = 2, 1, 1$ or $b = 2, 2$. Writing lists of blocks by
juxtaposition, with commas between parts, $d_1 = [ab]$, $d_2 = [abb]$, $d_3 = [abb, ab, ab]$ and
$d_4 = [abb, ab, ab, abb, abb]$; for $n \ge 5$, if $d_{n-1} = [j, ab, ab]$ for a list $j$ then
$d_n = [j, ab, ab, j, abb]$, and if $d_{n-1} = [j, abb]$ then $d_n = [j, abb, j, ab, ab]$. The
digit string of $d_n$ is the concatenation of its blocks. For $n = 0$ the list is empty, a
placeholder.

## Sources

- Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article A75, Definition 7.
