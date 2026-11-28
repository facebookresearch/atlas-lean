# Optimal sizes of tiny pointers

For every $\delta \in (0, 1)$ there are dereference tables on $n$ slots with load factor at least $1 - \delta$, in which each allocation succeeds and each update takes constant time with high probability, whose tiny pointers have size $O(\log \log \log n + \log \delta^{-1})$ bits in the fixed-size case (Theorem 1) and $O(P + \log \delta^{-1})$ bits in the variable-size case, where $\Pr[P \ge i] \le 2^{-2^{\Omega(i)}}$, so $O(1 + \log \delta^{-1})$ in expectation (Theorem 2). Conversely, for a universe of sufficiently large polynomial size and load factor $1 - \delta = \Omega(1)$, fixed-size tiny pointers need $\Omega(\log \log \log n + \log \delta^{-1})$ bits (Theorem 4) and variable-size ones $\Omega(\log \delta^{-1})$ expected bits (Theorem 3).

## Proof sketch

For fixed-size pointers, a primary *load-balancing table* hashes each key to one bucket of $\Theta(\delta^{-2}\log\delta^{-1})$ slots and stores the offset, $O(\log \delta^{-1})$ bits, at load factor $1 - \Theta(\delta^2)$; the few allocations that fail there go to a secondary power-of-two-choices table on $\delta n/2$ slots with buckets of $\Theta(\log\log n)$ slots at load factor $\Theta(1/\log\log n)$, whose pointers name one of two buckets and an offset in $O(\log\log\log n)$ bits. For variable-size pointers, the same primary/secondary split reduces the problem to a table of constant load factor, built from containers of $\Theta(\log n)$ slots, each a sequence of load-balancing tables with overflow arrays, whose pointer sizes have a doubly exponential tail.

## Depends on

- [Tiny pointers and dereference tables](tiny-pointer.md)

## Proof depends on

- [Maximum load of balls into bins](../../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Tiny Pointers", SODA (2023); ACM Transactions on Algorithms (2025), arXiv:2111.12800.
