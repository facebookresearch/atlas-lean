# Unit: an element with a two-sided inverse

An element $u$ of a ring $R$ with identity $1 \ne 0$ is a unit if some $v \in R$ satisfies $uv = vu = 1$. Mathlib defines this for any monoid, packaging the inverse into a bundled unit. Let $M$ be a monoid, a set with an associative multiplication and an identity $1$. A bundled unit of $M$ is a pair $(u, v)$ of elements of $M$ with $uv = 1$ and $vu = 1$. An element $a \in M$ *is a unit* when $a$ is the first component of some bundled unit, that is, when there is $b \in M$ with $ab = 1$ and $ba = 1$. Both identities are required: in a general monoid an element can have an inverse on one side only. No commutativity is assumed, and the condition $1 \ne 0$ plays no role. Being a unit is a property of an element, distinct from the group of all units. The multiplication of a ring $R$ with identity $1 \ne 0$ makes $R$ a monoid, which gives the familiar definition.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for bundled units: an element together with a two-sided inverse: `Units`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Units/Defs.lean#L46-L57.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the description of units by a two-sided inverse: `isUnit_iff_exists`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Units/Defs.lean#L367-L373.
