# Ideal of a Lie algebra

An ideal of a Lie algebra over a field is a subspace closed under bracketing with arbitrary elements of the algebra. Mathlib defines ideals of Lie algebras over any commutative ring. Let $R$ be a commutative ring and $L$ a Lie algebra over $R$. An *ideal* of $L$ is an $R$-submodule $I \subseteq L$ such that $[x, y] \in I$ for all $x \in L$ and $y \in I$; equivalently, a Lie submodule of $L$ for the action of $L$ on itself by the bracket. Since $[y, x] = -[x, y]$ and $I$ is closed under negation, also $[y, x] \in I$. No finiteness is assumed. Over a field $F$ the $F$-submodules of $L$ are its vector subspaces, which gives the familiar definition.

## Sources

- James E. Humphreys, Introduction to Lie Algebras and Representation Theory, Graduate Texts in Mathematics 9, Springer-Verlag, 1972.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for Lie submodules: `LieSubmodule`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Lie/Submodule.lean#L40-L43.
