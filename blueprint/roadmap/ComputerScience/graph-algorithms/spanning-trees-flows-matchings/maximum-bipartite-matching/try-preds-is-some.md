# When trying candidates finds a path

For a right vertex $j$, a test $\mathrm{ok}$ on left vertices, a map $\pi$ giving each left vertex
an optional right vertex, and a search $s$ taking a right vertex and a dead set (a set of right
vertices) to an optional path and a new dead set, write $T(l, D)$ for the optional path and the
dead set returned by trying the left vertices of the list $l$ as predecessors of $j$, starting from
the dead set $D$.
Suppose some vertex of $l$ passes $\mathrm{ok}$, and for every vertex $i$ of $l$ passing
$\mathrm{ok}$ and every right vertex $j'$ with $\pi(i) = j'$, the search $s(j', D)$ finds a path.
Then $T(l, D)$ finds a path.

Only the initial dead set matters: it does not change before the first vertex passing
$\mathrm{ok}$.
