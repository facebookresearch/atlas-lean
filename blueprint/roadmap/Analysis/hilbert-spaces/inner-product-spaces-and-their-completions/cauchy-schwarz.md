# Cauchy–Schwarz inequality in an inner product space

Let $V$ be a vector space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ with an inner product $\langle \cdot, \cdot \rangle$, or more generally with a positive semidefinite Hermitian form, for which $\langle v, v \rangle = 0$ may also hold for some $v \neq 0$. For a vector $v$, write $\|v\| = \sqrt{\langle v, v \rangle}$. Then for all $x, y \in V$,

$$|\langle x, y \rangle| \le \|x\| \, \|y\|.$$

The inequality does not depend on which argument of the form is taken to be conjugate-linear.

## Sources

- Stephen H. Friedberg, Arnold J. Insel and Lawrence E. Spence, Linear Algebra, 4th ed., Prentice Hall, 2003.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for inner product spaces over a seminormed additive group, conjugate-linear in the first argument, with $\|v\|^2$ the real part of $\langle v, v \rangle$: `InnerProductSpace`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/InnerProductSpace/Defs.lean#L110-L119.
