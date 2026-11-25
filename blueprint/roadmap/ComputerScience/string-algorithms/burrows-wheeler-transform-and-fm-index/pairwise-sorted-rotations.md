# Rows of the Burrows–Wheeler matrix are sorted

Let $t$ be a text over a linearly ordered alphabet, $t\bot$ the text followed by a sentinel smaller
than every letter, and $R$ the list of sorted rotations of $t$. The rows of the Burrows–Wheeler
matrix are sorted: for all rows $r < r'$, the rotation of $t\bot$ starting at $R[r]$ is
lexicographically at most the rotation starting at $R[r']$.
