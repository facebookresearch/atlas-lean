# The monotone chain hull of non-collinear points turns strictly left at every vertex

Let
$\Bbbk$ be a linearly ordered field and write $(u_1, u_2) \times (v_1, v_2) = u_1 v_2 - v_1 u_2$
for the cross product on $\Bbbk^2$. Let $P$ be a list of points of $\Bbbk^2$ that is strictly
increasing in the lexicographic order on $(x, y)$, and suppose the points of $P$ are not all
collinear: there are points $a, b, c$ of $P$ with $(b - a) \times (c - a) \ne 0$. Let $H$ be the
list of points returned by the monotone chain convex hull algorithm on $P$. Then the list
obtained from $H$ by appending its first two points (all of $H$ if $H$ has fewer than two points)
turns strictly left: any three consecutive points $q, r, s$ of it satisfy
$(r - q) \times (s - q) > 0$.

Read cyclically, this says the hull polygon turns strictly left at every vertex, including the
two vertices where the lower and upper chains meet.
