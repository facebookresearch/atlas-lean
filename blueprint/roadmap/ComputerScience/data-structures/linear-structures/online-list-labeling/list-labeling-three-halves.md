# Breaking the $\log^2 n$ barrier for list labeling

Against an oblivious adversary, for $m = (1 + \varepsilon) n$ with $\varepsilon = O(1)$, there is a randomized history-independent list-labeling algorithm with expected relabeling cost $O(\varepsilon^{-1}\log^{3/2} n)$ per insertion or deletion, which is $O(\log^{3/2} n)$ in the linear regime. Moreover, for all $\varepsilon$ between $n^{-1/3}$ and a sufficiently small positive constant, every history-independent algorithm has expected relabeling cost $\Omega(\varepsilon^{-1}\log^{3/2} n)$, so the bound is optimal among history-independent algorithms.

## Proof sketch

The algorithm starts from the history-independent variant of the classical solution, in which the root of every subtree of the window tree is a uniformly random element among the middle $O(k/\log n)$ of its $k$ elements, maintained by reservoir sampling. It enlarges this candidate set smoothly as a function of the subtree's density, to about a $1/\sqrt{\log n}$ fraction for most subtrees, so that roots are resampled less often. A *Zeno random walk*, a bounded walk whose step size shrinks near the boundary, models the densities met along a random root-to-leaf path and bounds the cost of a random insertion; history independence together with a random shift of the array then prevents the adversary from targeting the few slow regions.

## Depends on

- [History-independent list labeling](history-independent-list-labeling.md)
- [The online list-labeling problem](online-list-labeling.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, Hanna Komlós, William Kuszmaul, Nicole Wein, "Online List Labeling: Breaking the log^2 n Barrier", FOCS (2022), arXiv:2203.02763.
