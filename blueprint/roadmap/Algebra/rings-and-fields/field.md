# Field

A *field* is a commutative ring $F$ with identity, in which $1 \neq 0$, such that every nonzero element $a \in F$ has a multiplicative inverse $a^{-1}$, with $aa^{-1} = 1$. Under these axioms $0$ has no multiplicative inverse. In Mathlib, inversion is total: by convention $0^{-1} = 0$, so its division operation gives $a/0 = 0$. This value of $0^{-1}$ is a convention, not a multiplicative inverse of $0$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the convention 0⁻¹ = 0 and its consequence a/0 = 0: `DivisionRing.inv_zero`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Field/Defs.lean#L120-L121, and `div_zero`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/GroupWithZero/Basic.lean#L401.
