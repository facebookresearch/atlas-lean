# Randomized MIS requires nearly logarithmic rounds

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Every randomized LOCAL algorithm that computes a maximal independent set with probability at least $1/2$ on every $n$-vertex graph uses $\Omega\bigl(\sqrt{\log n / \log\log n}\bigr)$ rounds on some graph (with unbounded degree), and more strongly every randomized LOCAL algorithm with $o(\log n / \log\log n)$ rounds succeeds with only subconstant probability on some input. Thus the $O(\log n)$-round randomized algorithms of Luby and of Alon, Babai and Itai are optimal up to a $\log\log n$ factor.

## Proof sketch

The classical bound constructs graphs that are locally tree-like and indistinguishable within $t$ rounds while their independence structure differs, using cluster-tree constructions. The stronger bound starts from a $D$-regular graph with $D = \Theta(\log n)$ and girth $\Theta(\log_D n)$ and replaces each vertex by a dense gadget, so that the final graph is not locally tree-like; an indistinguishability argument across the gadget structure then shows that a fast algorithm cannot coordinate the gadgets consistently.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)
- [Luby's maximal independent set algorithm](../luby-s-maximal-independent-set-algorithm.md)

## Proof depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Sources

- F. Kuhn, T. Moscibroda, R. Wattenhofer, "Local Computation: Lower and Upper Bounds", Journal of the ACM 63(2) (2016).
- S. Khoury, A. Schild, "No Truly Sublogarithmic-Round Algorithm for Distributed MIS in the LOCAL Model", arXiv:2610.18215 (2026).
- N. Alon, L. Babai, A. Itai, "A fast and simple randomized parallel algorithm for the maximal independent set problem", Journal of Algorithms 7(4) (1986).
