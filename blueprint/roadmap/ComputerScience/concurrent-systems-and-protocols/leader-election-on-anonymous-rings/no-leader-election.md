# No deterministic leader election on an anonymous ring

On a synchronous ring of $n$ processes, in each round every process replaces its state by $\delta(\text{left neighbor's state}, \text{own state}, \text{right neighbor's state})$ for one deterministic transition $\delta$ shared by all processes. If $n \ge 2$, all processes start in the same state, and leadership is read off a process's state by a fixed predicate, then after any number of rounds it is never the case that exactly one process is the leader.

## Sources

- D. Angluin, "Local and global properties in networks of processors", *Proceedings of the 12th Annual ACM Symposium on Theory of Computing*, 1980.
- N. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 3.
