# Phase one: the status list is strictly sorted between the processed and remaining events

Fix a number $p_x$ in the field of coordinates. Suppose no segment is vertical (each segment's
left endpoint has smaller $x$-coordinate than its right endpoint) and every point common to two
distinct segments has $x$-coordinate at least $p_x$. Split the sorted list of events as $P$
followed by $Q$, where the endpoint of every event of $P$ has $x$-coordinate less than $p_x$, and
suppose running the sweep over $P$ from the empty status list reports no intersection and ends
with status list $T$. Let $x < p_x$ be at least the $x$-coordinate of the endpoint of every event
of $P$ and at most that of every event of $Q$. Then whenever segment $j$ comes before segment $k$
in $T$, the height at $x$ of the line through the endpoints of $j$ is less than that of the line
through the endpoints of $k$.
