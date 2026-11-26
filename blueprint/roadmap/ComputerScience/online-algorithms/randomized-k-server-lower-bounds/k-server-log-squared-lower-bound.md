# Some $(k+1)$-point metrics force $\Omega(\log^2 k)$ randomized k-server ratio

There exist, for infinitely many $k$, metric spaces with $k + 1$ points on which every randomized online $k$-server algorithm has competitive ratio $\Omega(\log^2 k)$ against oblivious adversaries.

## Proof sketch

Bubeck, Coester and Rabani construct a recursive family of metrics, in which each level consists of copies of the previous level placed at a much larger scale with a carefully balanced number of copies, together with a recursive adversary that forces an algorithm with $\alpha$ competitive ratio at one level to pay a factor $\Omega(\log k)$ more on the next. The construction is cast in the equivalent metrical task system on the hole position, and Yao's principle converts the random adversary into a lower bound against randomized algorithms.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Proof depends on

- [k-server on $k+1$ points is a metrical task system](k-server-on-k-plus-one-points.md)
- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753.
