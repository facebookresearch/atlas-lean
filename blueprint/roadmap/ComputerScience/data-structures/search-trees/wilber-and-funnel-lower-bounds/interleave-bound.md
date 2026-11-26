# Wilber's interleave (alternation) bound

Fix a static BST $T$ on the keys $[n]$, the *reference tree*. For a node $v$ of $T$ and an access sequence $X$, consider the subsequence of accesses to keys in the subtree of $v$ and label each such access $L$ if its key lies in the left subtree of $v$ or equals $v$, and $R$ if it lies in the right subtree. Let $\mathrm{alt}_v(X)$ be the number of indices at which consecutive labels differ. The *interleave bound* is $\mathrm{IB}_T(X) = \sum_{v \in T} \mathrm{alt}_v(X)$.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
