# Path reconstruction from BFS parents

Let $p$ be the predecessor function of a
breadth-first search forest, let $n$ be the length of its discovery order, and let $s$ and $t$ be
vertices. Starting from $v_k = t$, this walks back along $p$, setting $v_{i-1} = p(v_i)$,
until it reaches a vertex $v_0$ that tests equal to $s$, and returns the list
$v_0, v_1, \dots, v_k$. It returns no list if the walk meets a vertex that does not test equal to
$s$ and has no predecessor, or if none of the first $n + 1$ vertices $t, p(t), \dots$ of the walk
tests equal to $s$. The cost counts one unit for each test against $s$, each predecessor lookup
and each vertex prepended to the list.

The bound $n$ makes the walk terminate even when the predecessor table contains a cycle.
