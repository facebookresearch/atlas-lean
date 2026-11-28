# Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio

For every $k \ge 1$ there is a metric space with $k + 1$ points on which every randomized online $k$-server algorithm has competitive ratio $\Omega(\log^2 k)$ against oblivious adversaries.

## Proof sketch

Bubeck, Coester and Rabani work with the position of the hole (the point without a server), which the adversary can confine to any subset of points by requesting the others, and build shortest-path metrics on recursively defined graphs akin to diamond graphs: level $w + 1$ glues six copies of level $w$ in a cycle with two antipodal terminals $s$ and $t$. A random request sequence makes the hole travel from $s$ to $t$ through one of the two halves of the cycle, recursively paying the level-$w$ ratio along the way, while the choice of half stays uncertain long enough to force extra cost; issuing the inductive sequences in small chunks keeps the switching cost low, so that the ratio grows from $\alpha w^2$ to $\alpha (w+1)^2$ on metrics with $O(6^w)$ points. Yao's principle converts the random request sequence into a lower bound against randomized algorithms.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Proof depends on

- [k-server on $k+1$ points is a metrical task system](k-server-on-k-plus-one-points.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753, Sections 3 and 4 (Theorem 11).
