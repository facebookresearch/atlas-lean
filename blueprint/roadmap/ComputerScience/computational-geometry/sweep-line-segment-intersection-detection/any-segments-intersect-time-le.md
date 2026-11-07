# Running time of ANY-SEGMENTS-INTERSECT

Let $\Bbbk$ be a field with a linear order. For
every $n$ segments in $\Bbbk^2$, each given by its two endpoints, ANY-SEGMENTS-INTERSECT costs at
most $n^2 + 24n$, so it runs in time $O(n^2)$. Cost counts one unit per evaluation of DIRECTION
or ON-SEGMENT.

The bound comes from at most $n$ DIRECTION evaluations to place each segment in the list-based
status and at most three SEGMENTS-INTERSECT tests per segment.
