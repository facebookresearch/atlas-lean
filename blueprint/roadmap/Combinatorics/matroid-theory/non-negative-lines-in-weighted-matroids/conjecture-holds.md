# Non-negative points of a weighted rank-3 matroid are connected by non-negative lines

Let $n$
be a natural number, let $M$ be a simple matroid of rank $3$ on the ground set $\{0, \dots, n-1\}$
(every set of at most two points is independent) and let $a_0, \dots, a_{n-1}$ be real weights
with $a_0 + \dots + a_{n-1} \ge 0$. Then the graph on the points $i$ with $a_i \ge 0$, in which two
distinct points are adjacent when some line of $M$ (a flat of rank $2$) contains both and has
non-negative weight, the weight of a set being the sum of the weights of its points, is
connected.

Resolved true: for a matroid of rank $r$, a generic weight and a threshold $t \le \min\{0, w\}$,
where $w$ is the total weight, the proper flats of weight greater than $t$ form an
$(r - 3)$-connected poset (Adiprasito–Björner, Theorem 2.1, settling the Mikhalkin–Ziegler
conjecture); for $r = 3$, a small generic perturbation with $t$ slightly below $0$ gives the
connectivity of the non-negative points through non-negative lines. Shellability in the omitted
rank-$r$ part is open (their Open Problem 3.2).

## Sources

- K. A. Adiprasito, A. Björner, Filtered geometric lattices and Lefschetz section theorems over the tropical semiring, arXiv:1401.7301, https://arxiv.org/abs/1401.7301. Moved from `OpenConjectures/Combinatorics/WeightedMatroidNonnegativeLinesConnected`.
