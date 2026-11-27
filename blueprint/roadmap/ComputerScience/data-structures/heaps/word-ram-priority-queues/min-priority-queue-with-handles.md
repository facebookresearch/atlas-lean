# Bounded min-priority queue with handles

The *bounded min-priority queue with handles* with capacity $n$, keys below $U$ and values below $V$ has as state a partial map from handles $[n]$ to entries $(u, v)$. $\mathrm{insert}(u, v)$ is admissible when some handle is unused and returns some unused handle $h$, now mapped to $(u, v)$; $\mathrm{decreaseKey}(h, u')$ with $u'$ at most the current key of $h$ lowers it; $\mathrm{extractMin}$ removes and returns some entry of minimum key; $\mathrm{min}$ and $\mathrm{size}$ are queries. The choices of handle and of the extracted minimum are nondeterministic in the specification, so implementations may choose them. The indexed variant fixes the handle set to $[n]$ chosen by the caller and breaks ties by least handle.

## Depends on

- [State-transition specification of a data structure](../../data-structure-interfaces-and-refinement/state-transition-specification.md)
- [Indexed minimum queue](../indexed-minimum-priority-queue/indexed-min-queue.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- M. L. Fredman and R. E. Tarjan, "Fibonacci Heaps and Their Uses in Improved Network Optimization Algorithms", Journal of the ACM 34(3), pp. 596-615, 1987.
