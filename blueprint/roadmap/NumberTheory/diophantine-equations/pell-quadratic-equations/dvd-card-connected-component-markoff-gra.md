# Chen's theorem for Markoff graphs

Let $p > 3$ be a prime. The Markoff graph over
$\mathbb{Z}/p\mathbb{Z}$ has as vertices the nonzero triples $(x_0, x_1, x_2)$ of elements of
$\mathbb{Z}/p\mathbb{Z}$ with $x_0^2 + x_1^2 + x_2^2 = 3 x_0 x_1 x_2$, and two distinct
triples are adjacent when one is obtained from the other by a Vieta involution, which replaces
one coordinate $x_i$ by $3 x_j x_k - x_i$ and keeps the other two coordinates $x_j$, $x_k$,
where $\{i, j, k\} = \{0, 1, 2\}$. Every connected component of this graph has a number of
vertices divisible by $p$.

## Sources

- https://link.springer.com/article/10.1007/s00222-025-01346-9. Problem `dvd_card_connectedComponent_markoffGraph` of the lean-eval benchmark.
