# Sift-down from a node without children costs nothing

Let $a$ be an array over a
linearly ordered type and $i$ an index. If the smaller-child selection at $i$ in $a$ returns no
child, then sift-down from $i$, with cost counted as the pair (value comparisons, array swaps),
has cost $(0, 0)$: it makes no value comparisons and no array swaps.
