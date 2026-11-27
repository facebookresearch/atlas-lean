# Trying candidates keeps dead vertices dead

For a right vertex $j$, a test $\mathrm{ok}$ on left vertices, a map $\pi$ giving each left vertex
an optional right vertex, and a search $s$ taking a right vertex and a dead set (a set of right
vertices) to an optional path and a new dead set, write $T(l, D)$ for the optional path and the
dead set returned by trying the left vertices of the list $l$ as predecessors of $j$, starting from
the dead set $D$.
Suppose $s$ never shrinks the dead set: for every right vertex $j'$ and every dead set $d$, the
dead set returned by $s(j', d)$ contains $d$.
Then for every list $l$ of left vertices and every dead set $D$, the dead set of $T(l, D)$
contains $D$.
