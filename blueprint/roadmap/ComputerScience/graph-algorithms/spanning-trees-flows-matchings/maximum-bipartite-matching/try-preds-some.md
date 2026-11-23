# A path found by trying candidates comes from one candidate

For a right vertex $j$, a test $\mathrm{ok}$ on left vertices, a map $\pi$ giving each left vertex
an optional right vertex, and a search $s$ taking a right vertex and a dead set (a set of right
vertices) to an optional path and a new dead set, write $T(l, D)$ for the optional path and the
dead set returned by trying the left vertices of the list $l$ as predecessors of $j$, starting from
the dead set $D$.
Suppose $s$ never shrinks the dead set: for every right vertex $j'$ and every dead set $d$, the
dead set returned by $s(j', d)$ contains $d$.
If $T(l, D)$ returns a path $P$, then there are a vertex $i$ of $l$ with $\mathrm{ok}(i)$ and a
dead set $D_0$ containing $D$ such that either $\pi(i)$ is undefined and $P = [(i, j)]$, or
$\pi(i) = j'$ for a right vertex $j'$ and $s(j', D_0)$ returns a path $P'$ with $P$ equal to
$(i, j)$ followed by $P'$.
