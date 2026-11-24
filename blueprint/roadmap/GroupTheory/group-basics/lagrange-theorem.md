# Lagrange's theorem: the order of a group is the number of cosets of a subgroup times its order

Let $G$ be a group, let $H$ be a subgroup of $G$, and let $G/H$ be the set of left cosets $gH$ of $H$ in $G$. Then $|G| = |G/H| \cdot |H|$, where the number of elements of an infinite set is taken to be $0$. In particular, if $G$ is finite, then the order $|H|$ divides the order $|G|$, and the number of distinct left cosets of $H$ in $G$ is $|G|/|H|$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the cardinality of a type as a natural number, $0$ for an infinite type: `Nat.card`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/SetTheory/Cardinal/Finite.lean#L37-L40.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the quotient of a group by a subgroup as the set of left cosets: `QuotientGroup.leftRel`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/GroupTheory/Coset/Defs.lean#L60-L67.
