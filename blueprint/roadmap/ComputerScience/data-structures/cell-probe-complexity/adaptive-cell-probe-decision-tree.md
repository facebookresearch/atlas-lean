# Adaptive cell-probe decision tree

Let $S, w \ge 1$. A *memory* is a function $m : [S] \to \{0, 1, \dots, 2^w - 1\}$. An *adaptive cell-probe tree* returning values in $R$ is a finite rooted tree in which each internal node either *reads* a cell $i \in [S]$ and has one child for each of the $2^w$ possible contents, or *writes* a value $v < 2^w$ to a cell $i$ and has one child; each leaf is labelled by an element of $R$. Running the tree on a memory follows the branch selected by each read, updates the memory at each write, and returns the leaf label and the final memory. The *probes* of a run are the number of read and write nodes on its path; the *depth* of the tree is the maximum number of probes. All computation other than probes is free.

## Depends on

- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- A. C.-C. Yao, "Should Tables Be Sorted?", Journal of the ACM 28(3), pp. 615-628, 1981.
- M. Minsky and S. Papert, "Perceptrons: An Introduction to Computational Geometry", MIT Press, 1969.
