# The optimum changes with probability at most d/i

Run Seidel's randomized incremental algorithm on $n$ halfspaces in $\mathbb{R}^d$ in general position with a bounded objective, inserted in uniformly random order, and let $p_i$ be the probability that the optimum vertex changes when the $i$-th halfspace is inserted ($d + 1 \le i \le n$). Then $p_i \le d/i$. Indeed the optimum $v_i$ of the first $i$ halfspaces depends only on that set, it is defined by $d$ of them, and it differs from $v_{i-1}$ only if one of these $d$ halfspaces was inserted last, which happens with probability $d/i$.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Proof depends on

- [A violated constraint contains the new optimum](a-violated-constraint-contains-the-new-optimum.md)

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 7, "Backwards Analysis for Randomized LP": the optimum changes if and only if one of the $d$ defining halfspaces was the last inserted, so $p_i = d/i$
