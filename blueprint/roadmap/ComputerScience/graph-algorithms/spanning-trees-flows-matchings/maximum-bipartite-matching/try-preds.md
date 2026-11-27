# Trying the candidate predecessors of a right vertex

Let $j$ be a right vertex,
$\mathrm{ok}$ a test on left vertices, $\pi$ a map giving each left vertex an optional right vertex
(its partner, if any), and $s$ a search taking a right vertex and a dead set (a set of right
vertices) to an optional path, a list of pairs of a left and a right vertex, and a new dead set.
Given a list of left vertices and a dead set $D$, the procedure goes through the list in order,
skipping the vertices that fail $\mathrm{ok}$. At the first remaining vertex $i$: if $\pi(i)$ is
undefined, it returns the path $[(i, j)]$ and $D$; if $\pi(i) = j'$ and $s(j', D)$ finds a path
$P$, it returns the path $(i, j)$ followed by $P$, with the dead set returned by $s$; if
$s(j', D)$ finds no path, it continues with the rest of the list from the dead set returned by
$s$. When the list is exhausted, it fails and returns the current dead set with $j$ added.
