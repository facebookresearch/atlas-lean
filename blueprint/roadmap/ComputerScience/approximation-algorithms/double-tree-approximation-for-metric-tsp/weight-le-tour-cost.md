# A minimum spanning tree costs at most any tour

Let $d$ be a cost function on the
vertices with values in a linearly ordered additive commutative monoid that is symmetric, zero on
the diagonal, nonnegative and satisfies the triangle inequality. Let $V$ be a list of distinct
vertices. Let $T$ be a minimum spanning tree of $V$ for $d$: a rooted tree whose vertices are the
elements of $V$, each once, whose weight (the total cost of its edges) is at most that of every
such tree. Let $H$ be a tour of $V$, a list that is a permutation of $V$. Then the weight of $T$
is at most the cost of the closed tour $H$.

A tour minus its closing edge is a spanning path, which is a spanning tree.

## Sources

- CLRS Theorem 35.2, second half.
