# ANY-SEGMENTS-INTERSECT

Let $\Bbbk$ be a linearly ordered field. Given $n$ segments
$s_0, \dots, s_{n-1}$ in $\Bbbk^2$, each given by its two endpoints, write $l_t$, the left endpoint
of $s_t$, for its endpoint with the smaller $x$-coordinate, or for its first given endpoint when
both $x$-coordinates agree, and $r_t$, the right endpoint, for the other one. The procedure sorts
the $2n$ endpoints by $x$-coordinate, left endpoints before right endpoints at equal $x$, then by
$y$-coordinate, with remaining ties in increasing order of segment index. It then sweeps a
vertical line across them, starting with an empty status list of segments, kept from bottom to
top. At the left endpoint $l_i$ of $s_i$, let $P$ be the longest initial part of the status list
consisting of segments $s_t$ with $\mathrm{DIRECTION}(l_t, r_t, l_i) < 0$. Then $s_i$ is tested
with SEGMENTS-INTERSECT first against the segment just after $P$ and then against the last
segment of $P$, when these exist, and is inserted directly after $P$. At the right endpoint of
$s_i$, the segments just before and just after $s_i$ in the status list, when both exist, are
tested against each other and $s_i$ is deleted. The procedure returns true as soon as a test
succeeds and false after the last event. Cost counts one unit per evaluation of DIRECTION or
ON-SEGMENT (CLRS, third edition, Section 33.2).

The status is kept in a list rather than CLRS's red-black tree.
