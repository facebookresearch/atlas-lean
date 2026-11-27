# Classical $O(\log^2 n)$ list labeling

In the linear regime $m = (1 + \Theta(1))\,n$, there is a deterministic list-labeling algorithm with amortized relabeling cost $O(\log^2 n)$ per insertion or deletion. In the completely packed case $m = n$, where $n$ items are inserted one by one until the array is full, there is a deterministic algorithm with total cost $O(n \log^3 n)$, that is, amortized cost $O(\log^3 n)$ per insertion.

## Proof sketch

Itai, Konheim and Rodeh impose a balanced tree of windows on the array and keep the densities of sibling windows within a factor $1 \pm O(1/\log n)$ of each other, evenly redistributing a window whenever this invariant breaks; each window is then rebuilt $O(\log n)$ times more often than in an ordinary weight-balanced tree, giving $O(\log^2 n)$ amortized moves. For $m = n$, Zhang's algorithm, simplified by Bird and Sadnicki, adapts the density thresholds to the vanishing slack and loses one further logarithmic factor.

## Depends on

- [The online list-labeling problem](online-list-labeling.md)

## Proof depends on

- [Amortized cost of packed memory arrays](../../../memory-hierarchy-algorithms/cache-oblivious-search-trees-and-layouts/packed-memory-array-cost.md)

## Sources

- Alon Itai, Alan G. Konheim, Michael Rodeh, "A Sparse Table Implementation of Priority Queues", ICALP (1981).
- Richard S. Bird, Stefan Sadnicki, "Minimal On-Line Labelling", Information Processing Letters 101(1) (2007).
- Jan Bulánek, Michal Koucký, Michael Saks, "Tight Lower Bounds for the Online Labeling Problem", STOC (2012); SIAM Journal on Computing 44(6) (2015), arXiv:1112.5636.
