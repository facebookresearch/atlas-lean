# Phase two: inserting left endpoints on a vertical line keeps the status weakly sorted

Fix a number $p_x$ in the field of coordinates. Suppose no segment is vertical (each segment's
left endpoint has smaller $x$-coordinate than its right endpoint) and every point common to two
distinct segments has $x$-coordinate at least $p_x$. Split the sorted list of events as $P_1$,
then $P_2$, then $Q$, where the endpoint of every event of $P_1$ has $x$-coordinate less than
$p_x$, every event of $P_2$ is a left endpoint with $x$-coordinate equal to $p_x$, and the
endpoint of every event of $Q$ has $x$-coordinate at least $p_x$. If running the sweep over $P_1$
followed by $P_2$ from the empty status list reports no intersection and ends with status list
$T$, then whenever segment $j$ comes before segment $k$ in $T$, the height at $p_x$ of the line
through the endpoints of $j$ is at most that of the line through the endpoints of $k$.
