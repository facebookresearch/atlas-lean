# Breaking the $\log^2 n$ barrier for list labeling

For $m = (1 + \varepsilon) n$ with $\varepsilon = O(1)$, there is a randomized history-independent list-labeling algorithm with expected relabeling cost $O(\varepsilon^{-1}\log^{3/2} n)$ per operation, which is $O(\log^{3/2} n)$ in the linear regime. Moreover, for all $\varepsilon$ between $n^{-1/3}$ and a sufficiently small positive constant, every history-independent algorithm has expected relabeling cost $\Omega(\varepsilon^{-1}\log^{3/2} n)$, so the bound is optimal among history-independent algorithms.

## Proof sketch

The array is recursively divided into windows whose boundaries are chosen by a random process that depends only on the current set, making the state history independent. Randomization lets the boundary between two windows sit at a random rank within a range of width about $\sqrt{\log n}$ times the window's slack, so that an adversary cannot concentrate insertions at a boundary; balancing the probability of moving a boundary against the cost of rebuilding gives $\log^{3/2} n$ in place of $\log^2 n$.

## Depends on

- [History-independent list labeling](history-independent-list-labeling.md)
- [Tight lower bounds for deterministic list labeling](deterministic-list-labeling-lower-bound.md)

## Proof depends on

- [History-independent list labeling](history-independent-list-labeling.md)
- [Tight lower bounds for deterministic list labeling](deterministic-list-labeling-lower-bound.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
