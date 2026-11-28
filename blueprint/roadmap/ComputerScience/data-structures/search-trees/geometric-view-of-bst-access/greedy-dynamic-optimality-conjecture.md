# Greedy dynamic optimality conjecture

The *Greedy conjecture* asserts that there is an absolute constant $c$ such that for every $n$ and every access sequence $X \in [n]^m$ with $m \ge n$, the cost of geometric Greedy on $X$ is at most $c \cdot \mathrm{OPT}(X)$. Since online arborally satisfying algorithms convert to online BSTs with a constant-factor loss, it would imply the existence of a dynamically optimal online BST.

## Depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Online arborally satisfying algorithms yield online BSTs](online-geometry-to-online-bst.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
- Joan M. Lucas, "Canonical Forms for Competitive Binary Search Tree Algorithms", Rutgers University Technical Report DCS-TR-250 (1988).
- J. Ian Munro, "On the Competitiveness of Linear Search", ESA (2000).
