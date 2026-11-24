# Spectral radius formula in a complex Banach algebra

Let $A$ be a complex Banach algebra with identity, that is, a complete normed ring with identity that is a normed algebra over $\mathbb{C}$, and let $a \in A$. Let $r(a)$ be the spectral radius of $a$: the supremum of $|\lambda|$ over $\lambda$ in the spectrum $\sigma(a)$, taken in $[0, +\infty]$, where the supremum of the empty set is $0$. Then $\|a^n\|^{1/n} \to r(a)$ in $[0, +\infty]$ as $n \to \infty$. When $A \neq \{0\}$, the spectrum $\sigma(a)$ is nonempty and compact, so the supremum is the maximum of $|\lambda|$ over $\lambda \in \sigma(a)$. When $A = \{0\}$, the spectrum is empty and $r(a) = 0$.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the spectral radius as a supremum in $[0, +\infty]$, which in a unital algebra may be taken over the spectrum: `spectralRadius`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L70-L84.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the nonemptiness of the spectrum in a nonzero complex Banach algebra: `spectrum.nonempty`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean#L156-L159.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for its compactness: `spectrum.isCompact`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Algebra/Spectrum.lean#L201-L202.
