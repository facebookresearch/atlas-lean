# Child selection at a node without children costs nothing

Let $a$ be an array over a
linearly ordered type and $i$ an index. If the smaller-child selection at $i$ in $a$ returns no
child, then the timed child selection at $i$, with cost counted as the pair (value comparisons,
array swaps), has cost $(0, 0)$.
