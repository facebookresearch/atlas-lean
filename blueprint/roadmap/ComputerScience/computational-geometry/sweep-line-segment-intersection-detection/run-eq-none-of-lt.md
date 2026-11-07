# Sweep completeness when the leftmost intersection is inside both segments

Let $n$
segments in the plane over a linearly ordered field be given, where $z_1$ is the abscissa of a
point $z$ and segment $i$ has left endpoint $l_i$ and right endpoint $r_i$ with
$(l_i)_1 < (r_i)_1$, and suppose no point lies on three distinct segments. Let $a \ne b$ be
segments that share a point $p$ such that every point shared by two distinct segments has
abscissa at least $p_1$, and suppose $(l_a)_1 < p_1$ and $(l_b)_1 < p_1$. Then the sweep, run on
the sorted list of endpoint events from the empty status list, reports an intersection.

Just before the sweep line reaches $p$, the segments $a$ and $b$ are neighbours on the status
list, so they were tested.
