# Simple Lie algebra

A Lie algebra $L$ over a field is simple when it is not abelian, so that $[L, L] \ne 0$, and its only ideals are $0$ and $L$. Mathlib defines this more generally, for Lie algebras over a commutative ring. Let $R$ be a commutative ring and $L$ a Lie algebra over $R$. Then $L$ is *simple* when both of the following hold. Every Lie ideal of $L$, that is, every $R$-submodule $I$ of $L$ with $[x, y] \in I$ for all $x \in L$ and $y \in I$, is either $0$ or $L$. And $L$ is not abelian: $[x, y] \ne 0$ for some $x, y \in L$. Both clauses are needed: the zero Lie algebra and a one-dimensional abelian Lie algebra have no ideals other than $0$ and themselves, but they are not simple. Taking $R$ to be a field gives the familiar definition.

## Sources

- James E. Humphreys, Introduction to Lie Algebras and Representation Theory, Graduate Texts in Mathematics 9, Springer-Verlag, 1972.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for Lie ideals, the Lie submodules of the adjoint module: `LieIdeal`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Lie/Ideal.lean#L42-L46.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for abelian Lie algebras, in which all brackets vanish: `IsLieAbelian`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Lie/Abelian.lean#L39-L57.
