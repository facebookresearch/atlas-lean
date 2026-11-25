# Every finite-dimensional real or complex inner product space has an orthonormal basis

Let $V$ be a finite-dimensional inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then $V$ has an orthonormal basis: a finite set $B \subseteq V$ that is a basis of $V$ and whose vectors have norm $1$ and are pairwise orthogonal. For $V = \{0\}$, $B$ is empty.

Mathlib encodes an orthonormal basis indexed by a finite set $\iota$ as a linear isometric isomorphism from $V$ to $\mathbb{K}^\iota$ with its standard inner product; its basis vectors are the preimages of the standard basis vectors of $\mathbb{K}^\iota$. These data correspond exactly to bases of $V$ indexed by $\iota$ that consist of pairwise orthogonal unit vectors.

## Sources

- Stephen H. Friedberg, Arnold J. Insel and Lawrence E. Spence, Linear Algebra, 4th ed., Prentice Hall, 2003, §6.2, Theorem 6.5, pp. 346–347, for nonzero spaces.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the encoding of an orthonormal basis: `OrthonormalBasis`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L368-L372.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for its basis vectors as an orthonormal family: `OrthonormalBasis.orthonormal`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L426-L427.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for its basis vectors as a basis: `OrthonormalBasis.toBasis`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L457-L462.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the converse construction from an orthonormal basis in the usual sense: `Module.Basis.toOrthonormalBasis`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L579-L582.
