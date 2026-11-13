# Smallest child in a $d$-ary heap array

Let $a$ be an array of length $|a|$ over a linearly
ordered type and let $d$ and $i$ be natural numbers. The children of $i$ are the indices
$d i + k + 1$ for $0 \le k < d$, and a child is valid when it is below $|a|$. The smallest child
of $i$ is the valid child of $i$ with the least entry, taking the smallest offset $k$ among ties,
or nothing if $i$ has no valid child.
