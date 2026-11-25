# The sweep status holds the active segments

Let $P$ be an initial part of the sorted list
of events. If running the sweep over $P$ from the empty status list reports no intersection and
ends with status list $T$, then $T$ has no repeated entries, and a segment $j$ belongs to $T$
exactly when the left endpoint event of $j$ is in $P$ and the right endpoint event of $j$ is not.
