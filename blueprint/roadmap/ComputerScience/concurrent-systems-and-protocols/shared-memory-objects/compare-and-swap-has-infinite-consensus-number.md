# Compare-and-swap has infinite consensus number

For every $n$, wait-free consensus among $n$ processes can be solved with a single compare-and-swap register initialized to a special value $\bot$: each process attempts to swap $\bot$ for its input and decides the value held by the register afterwards. Hence compare-and-swap has consensus number $\infty$.

## Depends on

- [Consensus number](consensus-number.md)

## Sources

- M. Herlihy, "Wait-free synchronization", *ACM Transactions on Programming Languages and Systems* 13(1):124–149, 1991, Theorem 5
