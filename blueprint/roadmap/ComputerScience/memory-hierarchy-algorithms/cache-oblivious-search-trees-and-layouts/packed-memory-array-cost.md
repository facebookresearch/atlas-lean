# Amortized cost of packed memory arrays

A packed memory array on $N$ elements supports insertions and deletions with $O(\log^2 N)$ amortized element moves, and therefore $O\!\left(1 + \frac{\log^2 N}{L}\right)$ amortized cache misses in the ideal-cache model, because every redistribution is a scan of a contiguous window; scanning $K$ consecutive elements starting from a known array position costs $O(1 + K/L)$ misses. A range query that must first find the position of its first key pays that search in addition.

## Proof sketch

After a window at height $d$ is rebalanced, its density is strictly inside the thresholds of its children by a gap of $\Theta(1/\log N)$ relative density, so $\Omega(|W|/\log N)$ insertions into the window must occur before it is rebalanced again. Charging the $O(|W|)$ moves of the rebalance to those insertions costs $O(\log N)$ per insertion per level, and there are $O(\log N)$ levels.

## Depends on

- [Packed memory arrays](packed-memory-array.md)
- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000), Theorem 2.5.
