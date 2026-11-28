# Ring, not necessarily with an identity element

A *ring* in the sense that does not require a multiplicative identity is a set $R$ with two binary operations, addition $+$ and multiplication (written $ab$), satisfying three conditions. First, $(R, +)$ is an abelian group. Second, multiplication is associative: $(ab)c = a(bc)$ for all $a, b, c \in R$. Third, both distributive laws hold: $(a+b)c = ac + bc$ and $a(b+c) = ab + ac$ for all $a, b, c \in R$. Neither commutativity of multiplication nor a multiplicative identity is required, and neither is excluded: a ring with identity, or a commutative ring, is in particular a ring in this sense. The identities $0a = a0 = 0$ follow from distributivity and cancellation in $(R, +)$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004, §7.1, p. 223.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the axioms of an associative ring without an identity requirement, including $0a = a0 = 0$: `NonUnitalRing`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Ring/Defs.lean#L119-L132.
