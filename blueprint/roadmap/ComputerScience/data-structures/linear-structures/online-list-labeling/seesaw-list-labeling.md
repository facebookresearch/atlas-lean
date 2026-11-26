# Nearly optimal list labeling

In the linear regime $m = (1 + \Theta(1)) n$, the randomized *See-Saw* algorithm achieves expected amortized relabeling cost $O(\log n \cdot (\log\log n)^{O(1)})$ per operation. Since every randomized list-labeling algorithm in this regime has expected amortized cost $\Omega(\log n)$, the bound is optimal up to a $(\log\log n)^{O(1)}$ factor, despite several lower bounds ruling out such costs for deterministic, smooth and history-independent algorithms; in particular history dependence is necessary to go below $\log^{3/2} n$.

## Proof sketch

The See-Saw algorithm maintains the windows of a hierarchical scheme but, instead of rebalancing a window in response to density alone, it uses randomized *predictions* of where future insertions will concentrate, derived from the observed history, to allocate slack unevenly between sibling windows; a careful amortization shows that each insertion is charged $(\log\log n)^{O(1)}$ at each of $O(\log n)$ scales, with the history-independent lower bound circumvented because the allocation depends on past operations.

## Depends on

- [Breaking the $\log^2 n$ barrier for list labeling](list-labeling-three-halves.md)

## Proof depends on

- [Breaking the $\log^2 n$ barrier for list labeling](list-labeling-three-halves.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, Michal Koucký, William Kuszmaul, Michael Saks, "Nearly Optimal List Labeling", FOCS (2024).
- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
