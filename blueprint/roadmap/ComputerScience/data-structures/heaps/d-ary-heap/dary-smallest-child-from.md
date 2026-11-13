# Smallest child among the offsets from $s$

Let $a$ be an array over a linearly ordered
type, of length $|a|$, let $d$, $i$ and $s$ be natural numbers, and call $d i + k + 1$ the child
of $i$ at offset $k$. Scanning the offsets $s, s + 1, \dots, d - 1$, this returns the index of a
scanned child of $i$ below $|a|$ whose entry in $a$ is least among those, taking the smallest
offset among ties, or nothing if no scanned child index is below $|a|$.
