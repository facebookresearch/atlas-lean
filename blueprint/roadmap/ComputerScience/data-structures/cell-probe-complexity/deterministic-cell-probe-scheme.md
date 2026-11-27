# Deterministic dynamic cell-probe scheme

A *deterministic cell-probe scheme* for an operation set $\mathsf{Op}$ with result sets $\mathsf{Res}(o)$ in $S$ cells of $w$ bits consists of an initial memory $m_0$ and, for each $o \in \mathsf{Op}$, an adaptive cell-probe tree $T_o$ with values in $\mathsf{Res}(o)$. The state between operations is the memory alone (total space $S w$ bits). A sequence $o_1, \dots, o_t$ is run by applying $T_{o_1}, \dots, T_{o_t}$ in order; its *probe count* is the total number of probes. A *step-indexed* scheme is the relaxation in which the tree for the $j$-th operation may also depend on the index $j$.

A scheme *implements* a deterministic specification on a set of admissible histories if, on each such history, every returned value equals the specified answer.

## Depends on

- [Adaptive cell-probe decision tree](adaptive-cell-probe-decision-tree.md)
- [State-transition specification of a data structure](../data-structure-interfaces-and-refinement/state-transition-specification.md)

## Sources

- P. B. Miltersen, "Cell Probe Complexity - a Survey", Advances in Data Structures Workshop (FSTTCS pre-conference workshop), 1999.
- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.
