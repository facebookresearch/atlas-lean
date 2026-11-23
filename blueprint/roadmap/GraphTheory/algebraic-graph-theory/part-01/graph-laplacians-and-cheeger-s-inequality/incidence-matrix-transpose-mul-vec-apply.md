# The transposed incidence matrix gives potential differences across arcs

Let $V$ and $E$ be finite sets of nodes and arcs, each arc $e$ running from its tail $t(e)$ to its head $h(e)$; loops $t(e) = h(e)$ and parallel or antiparallel arcs are allowed. Let $B$ be the head-positive incidence matrix, the real $V \times E$ matrix with $B_{v e} = [h(e) = v] - [t(e) = v]$, so that a loop gives a zero column. For every potential $x : V \to \mathbb{R}$ and every arc $e$,

$$(B^{\mathsf T} x)_e = x(h(e)) - x(t(e)).$$

For a loop both sides are $0$.
