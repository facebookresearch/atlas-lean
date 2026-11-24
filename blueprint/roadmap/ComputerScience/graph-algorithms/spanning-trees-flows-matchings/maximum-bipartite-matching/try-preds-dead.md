# Where newly dead vertices come from

For a right vertex $j$, a test $\mathrm{ok}$ on left vertices, a map $\pi$ giving each left vertex
an optional right vertex, and a search $s$ taking a right vertex and a dead set (a set of right
vertices) to an optional path and a new dead set, write $T(l, D)$ for the optional path and the
dead set returned by trying the left vertices of the list $l$ as predecessors of $j$, starting from
the dead set $D$.
Suppose $s$ never shrinks the dead set: for every right vertex $j'$ and every dead set $d$, the
dead set returned by $s(j', d)$ contains $d$.
Let $E$ be the dead set of $T(l, D)$ and let $y$ be a right vertex in $E$ but not in $D$. Then
either $T(l, D)$ finds no path and $y = j$, or there are a vertex $i$ of $l$ passing
$\mathrm{ok}$, a right vertex $j'$ and a dead set $d$ containing $D$ such that $\pi(i) = j'$,
$y \notin d$, $y$ is in the dead set returned by $s(j', d)$, and that dead set is contained in
$E$.
