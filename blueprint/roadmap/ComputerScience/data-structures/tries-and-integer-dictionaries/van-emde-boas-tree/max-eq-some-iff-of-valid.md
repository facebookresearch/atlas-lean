# Correctness of the van Emde Boas maximum query

Let $m$ be a natural number, let $t$ be a
valid van Emde Boas tree over the universe $\{0, 1, \dots, m^2 - 1\}$ and let $x$ be an element of
the universe. The maximum query on $t$ returns $x$ if and only if $x$ is a member of $t$ and
$y \le x$ for every member $y$ of $t$.
