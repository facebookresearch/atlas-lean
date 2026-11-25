# Soundness of the any-segments-intersect sweep

Let $S$ be a family of $n$ segments in
$K^2$, $K$ a linearly ordered field, and split the sorted list of their $2n$ endpoint events as
$P$ followed by $Q$. If running the sweep over $P$ from the empty status list succeeds with status
list $T$, and running it over $Q$ from $T$ reports an intersection, then there are two distinct
indices $i \ne j$ such that segments $i$ and $j$ meet.

In particular, when the sweep over all the events reports an intersection, two distinct segments
meet.
