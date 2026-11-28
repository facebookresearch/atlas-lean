# Wilber's first lower bound

For every reference tree $T$ on $[n]$ and every access sequence $X$, $\mathrm{OPT}(X) \ge \frac12 \mathrm{IB}_T(X) - n$.

## Proof sketch

For each node $v$ of $T$, consider the *transition point* of $v$ in the optimal tree at each time: the node of minimum depth whose search path passes from the left region of $v$ to the right region. Each alternation in the labels at $v$ forces the access to touch the current transition point of $v$, transition points of distinct nodes $v$ are distinct at any fixed time, and a transition point changes only when it is touched; a counting argument then charges each alternation to a touch, with the factor $\frac12$ and the additive $n$ accounting for the initial tree.

## Depends on

- [Wilber's interleave (alternation) bound](interleave-bound.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
