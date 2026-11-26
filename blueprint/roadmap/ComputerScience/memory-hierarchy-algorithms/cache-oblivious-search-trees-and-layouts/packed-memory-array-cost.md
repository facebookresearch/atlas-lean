# Amortized cost of packed memory arrays

A packed memory array on $N$ elements supports insertions and deletions with $O(\log^2 N)$ amortized element moves, and therefore $O\!\left(1 + \frac{\log^2 N}{L}\right)$ amortized cache misses in the ideal-cache model, because every redistribution is a scan of a contiguous window; range queries returning $K$ elements cost $O(1 + K/L)$ misses.

## Proof sketch

After a window at height $d$ is rebalanced, its density is strictly inside the thresholds of its children by a gap of $\Theta(1/\log N)$ relative density, so $\Omega(|W|/\log N)$ insertions into the window must occur before it is rebalanced again. Charging the $O(|W|)$ moves of the rebalance to those insertions costs $O(\log N)$ per insertion per level, and there are $O(\log N)$ levels.

## Depends on

- [Packed memory arrays](packed-memory-array.md)

## Proof depends on

- [Packed memory arrays](packed-memory-array.md)

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
