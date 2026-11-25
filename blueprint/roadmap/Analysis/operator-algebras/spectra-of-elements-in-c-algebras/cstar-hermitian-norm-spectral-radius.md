# The norm of a self-adjoint element of a unital C*-algebra equals its spectral radius

Let $A$ be a C\*-algebra with identity and let $h \in A$ be hermitian, that is, $h^* = h$. Then $\|h\| = r(h)$, where $r(h)$ is the spectral radius of $h$: the supremum of $|\lambda|$ over $\lambda$ in the spectrum $\sigma(h)$ of $h$ in $A$, taken in $[0, +\infty]$, where the supremum of the empty set is $0$.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- Cho-Ho Chu, *C\*-algebras*, lecture notes for a London Taught Course Centre postgraduate course, Queen Mary, University of London, https://www.ltcc.ac.uk/media/london-taught-course-centre/documents/c_algebra.pdf, Corollary 2.10, p. 8: the norm of a normal element of a C\*-algebra, in particular of a self-adjoint element, equals its spectral radius.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the spectral radius as a supremum of norms in [0, +∞], which is 0 for the empty set and in a unital algebra may be taken over the spectrum: `spectralRadius`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L70-L84.
