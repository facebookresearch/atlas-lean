# Classical $O(\log^2 n)$ list labeling

In the linear regime $m = (1 + \Theta(1))\,n$, there is a deterministic list-labeling algorithm with amortized relabeling cost $O(\log^2 n)$ per insertion or deletion; for $m = n$ (a completely packed array) amortized cost $O(\log^3 n)$ is achievable.

## Proof sketch

The packed-memory-array density-threshold scheme of Itai, Konheim and Rodeh achieves $O(\log^2 n)$ amortized moves; for $m = n$, the slack is too small for linear thresholds and a hierarchical variant with an extra logarithmic level of gaps attains $O(\log^3 n)$.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)
- [Amortized cost of packed memory arrays](../../../memory-hierarchy-algorithms/cache-oblivious-search-trees-and-layouts/packed-memory-array-cost.md)

## Proof depends on

- [The online list-labeling problem](online-list-labeling.md)
- [Amortized cost of packed memory arrays](../../../memory-hierarchy-algorithms/cache-oblivious-search-trees-and-layouts/packed-memory-array-cost.md)

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Jan Bulánek, Michal Koucký, Michael Saks, "Tight Lower Bounds for the Online Labeling Problem", STOC (2012); SIAM Journal on Computing 44(6) (2015), arXiv:1112.5636.
