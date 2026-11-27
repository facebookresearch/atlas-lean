# Sift-down with comparison and swap counts

For an array $a$ over a linearly ordered
type and an index $i$, timed sift-down returns an array together with a cost pair
(value comparisons, array swaps), where costs add componentwise. If the left child index
$2i+1$ is not a valid index of $a$, it returns $a$ at cost $(0, 0)$. Otherwise let $c$ be the
smaller child of $i$: the left child $2i+1$, unless the right child $2i+2$ is a valid index
and $a_{2i+2} < a_{2i+1}$, in which case $c = 2i+2$. Selecting $c$ costs one comparison when
$2i+2$ is a valid index and nothing otherwise. Comparing $a_c$ with $a_i$ costs one more
comparison. If $a_c < a_i$, the entries at $i$ and $c$ are swapped at the cost of one swap,
and the result and remaining cost are those of timed sift-down from $c$ in the swapped array;
otherwise the result is $a$.

Index arithmetic, bounds checks, pattern matching and recursive calls are free.
