# Symmetry is preserved on an anonymous ring

Let processes be indexed by $\mathbb{Z}/n$, process $i$ having left neighbor $i - 1$ and right neighbor $i + 1$, and in each synchronous round let every process replace its state by $\delta(\text{left neighbor's state}, \text{own state}, \text{right neighbor's state})$ for one deterministic transition $\delta$ shared by all processes. If all processes start in the same state, then after any number of rounds all processes are in the same state. This holds for every $n$; for $n \ge 1$ the processes form a ring of $n$ processes, while for $n = 0$ the index set is $\mathbb{Z}/0 = \mathbb{Z}$, an infinite line of processes indexed by the integers rather than a ring with no processes.

## Sources

- D. Angluin, "Local and global properties in networks of processors", *Proceedings of the 12th Annual ACM Symposium on Theory of Computing*, 1980.
- N. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 3.
