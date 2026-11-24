# Symmetry is preserved on an anonymous ring

On a synchronous ring of $n$ processes, in each round every process replaces its state by $\delta(\text{left neighbor's state}, \text{own state}, \text{right neighbor's state})$ for one deterministic transition $\delta$ shared by all processes. If all processes start in the same state, then after any number of rounds all processes are in the same state.

## Sources

- D. Angluin, "Local and global properties in networks of processors", *Proceedings of the 12th Annual ACM Symposium on Theory of Computing*, 1980.
- N. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 3.
