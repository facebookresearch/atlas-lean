# Matrix entries of a linear operator in an orthonormal basis

Let $V$ be a finite-dimensional inner product space over $\mathbb{R}$ or $\mathbb{C}$, whose inner product $\langle \cdot, \cdot \rangle$ is conjugate-linear in the first argument and linear in the second. Let $(v_i)_{i \in I}$ be an orthonormal basis of $V$ indexed by a finite set $I$, let $T$ be a linear operator on $V$, and let $A$ be the matrix of $T$ in this basis, whose $j$-th column is the coordinate vector of $T v_j$. Then $A_{ij} = \langle v_i, T v_j \rangle$ for all $i, j \in I$. With the opposite convention, an inner product linear in the first argument, the same number is written $\langle T v_j, v_i \rangle$.

## Sources

- Stephen H. Friedberg, Arnold J. Insel and Lawrence E. Spence, Linear Algebra, 4th ed., Prentice Hall, 2003, §6.2, Corollary to Theorem 6.5, p. 347, whose inner products are linear in the first argument (Theorem 6.1(b), p. 333), so that the entry is written there as ⟨T(v_j), v_i⟩.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the convention that the inner product is conjugate-linear in the first argument: `InnerProductSpace`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/Defs.lean#L118-L119.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the matrix of an operator in an orthonormal basis: `LinearMap.toMatrixOrthonormal`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/Adjoint.lean#L1033-L1037.
