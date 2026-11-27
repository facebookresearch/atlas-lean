# Values of the Luby sequence at complete prefixes

For every base $y \ge 2$ and $k \ge 1$, the term of the base-$y$ Luby sequence at index $2^k - 1$ equals $y^{k-1}$, and the sum of the first $2^k - 1$ terms of the base-$2$ sequence equals $k \cdot 2^{k-1}$.

## Proof sketch

The first value is the first case of the definition. For the sum, induct on $k$: by the second case, the prefix of length $2^{k} - 1$ consists of two copies of the prefix of length $2^{k-1} - 1$ followed by $2^{k-1}$, so its sum is $2 (k-1) 2^{k-2} + 2^{k-1} = k \cdot 2^{k-1}$.

## Depends on

- [The Luby restart sequence](luby-restart-sequence.md)

## Sources

- M. Luby, A. Sinclair and D. Zuckerman, "Optimal Speedup of Las Vegas Algorithms", Information Processing Letters 47(4), 1993.
- J. Huang, "The Effect of Restarts on the Efficiency of Clause Learning", Proceedings of the 20th International Joint Conference on Artificial Intelligence (IJCAI 2007), 2007.
