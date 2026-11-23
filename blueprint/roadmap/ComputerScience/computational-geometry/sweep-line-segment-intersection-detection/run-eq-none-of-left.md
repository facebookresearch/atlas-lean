# Sweep completeness when the leftmost intersection is a left endpoint

Let $n$ segments in
the plane over a linearly ordered field be given, where $z_1$ is the abscissa of a point $z$ and
segment $i$ has left endpoint $l_i$ and right endpoint $r_i$ with $(l_i)_1 < (r_i)_1$, and
suppose no point lies on three distinct segments. Let $a \ne b$ be segments such that $l_a$ lies
on segment $b$ and every point shared by two distinct segments has abscissa at least $(l_a)_1$.
If the left endpoint of $b$ comes before the left endpoint of $a$ in the sorted list of endpoint
events, then the sweep, run on that list from the empty status list, reports an intersection.

Inserting $a$ places it right next to $b$, so the two are tested.
