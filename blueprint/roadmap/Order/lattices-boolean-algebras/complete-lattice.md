# Complete lattice

A *complete lattice* is a partially ordered set $(L, \le)$ in which every subset $S \subseteq L$, including $\varnothing$ and $L$ itself, has a least upper bound $\sup S$ and a greatest lower bound $\inf S$. In particular $L$ is nonempty, since $\varnothing$ has a least upper bound. As a structure, a complete lattice carries as operations the supremum and the infimum of every subset, the join $x \vee y$ and the meet $x \wedge y$ of any two elements (their least upper and greatest lower bounds), and a greatest element $\top$ and a least element $\bot$; each of these operations is determined by the order.

## Sources

- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the supremum and infimum operations carried by the structure: `CompleteLattice`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/CompleteLattice/Defs.lean#L142-L143, with `CompleteSemilatticeSup` and `CompleteSemilatticeInf`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/CompleteLattice/Defs.lean#L63-L75.
