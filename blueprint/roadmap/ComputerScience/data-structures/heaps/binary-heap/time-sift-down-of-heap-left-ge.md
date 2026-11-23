# Sift-down from a leaf costs nothing

Let $a$ be an array over a linearly ordered type,
of size $|a|$, and let $i$ be an index with $|a| \le 2i+1$, so that the left child of $i$ is not
a valid index (this includes invalid indices $i$). Then timed sift-down from $i$ has cost pair
$(0, 0)$: it counts no comparisons and no swaps.
