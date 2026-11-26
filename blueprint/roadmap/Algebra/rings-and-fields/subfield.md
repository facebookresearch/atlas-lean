# Subfield

A subfield of a field $K$ is a subset $F$ that contains $0$ and $1$, is closed under addition, multiplication and negation, and contains the inverse $a^{-1}$ of each nonzero $a \in F$; with the operations of $K$ it is a field. Mathlib defines subfields more generally, in division rings. Let $K$ be a division ring: a ring with $1 \ne 0$, not necessarily commutative, in which every nonzero element has a multiplicative inverse. A *subfield* of $K$ is a subring $F$ of $K$, a subset that contains $0$ and $1$ and is closed under addition, negation and multiplication, such that $x^{-1} \in F$ for every $x \in F$. The case $x = 0$ adds no condition, since Mathlib sets $0^{-1} = 0$ and $0 \in F$. When $K$ is not commutative, a subfield in this sense is a division subring, which need not be commutative. When $K$ is a field, the conditions are exactly those of the familiar definition.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for subrings: subsets that contain $0$ and $1$ and are closed under addition, negation and multiplication: `Subring`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Ring/Subring/Defs.lean#L161-L165.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for division rings, with the convention $0^{-1} = 0$: `DivisionRing`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Field/Defs.lean#L116-L121.
