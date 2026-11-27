# Quotient group by a normal subgroup

Let $G$ be a group and let $N$ be a normal subgroup of $G$. Write $G/N$ for the set $\{gN : g \in G\}$ of left cosets of $N$ in $G$; two elements $x, y \in G$ have the same left coset exactly when $x^{-1}y \in N$. The *quotient group* $G/N$ is this set with the multiplication $(uN)(vN) = (uv)N$ for $u, v \in G$. The product does not depend on the choice of the representatives $u$ and $v$, because $N$ is normal, and with it $G/N$ is a group with identity $1N = N$ and inverse $(gN)^{-1} = g^{-1}N$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the group structure on the quotient of a group by a normal subgroup, defined through the congruence relation of left cosets: `QuotientGroup.Quotient.group`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L57-L73.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the quotient of a group by a subgroup as the set of classes of the left coset relation, in which x and y are related when x⁻¹y lies in the subgroup: `QuotientGroup.leftRel` and `QuotientGroup.instHasQuotientSubgroup`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/GroupTheory/Coset/Defs.lean#L59-L77 and https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/GroupTheory/Coset/Defs.lean#L90-L95.
