# Module over a semiring

Let $R$ be a semiring: a set with an addition and a multiplication that satisfy the axioms of a ring with identity, except that elements need not have additive inverses, together with $0r = r0 = 0$ for all $r \in R$. A *(left) module* over $R$, also called a semimodule when $R$ is not a ring, is a commutative monoid $(M, +)$ with identity $0$ together with a map $R \times M \to M$, $(r, m) \mapsto rm$, such that for all $r, s \in R$ and $m, n \in M$:

1. $(r + s)m = rm + sm$;
2. $r(m + n) = rm + rn$;
3. $(rs)m = r(sm)$;
4. $1m = m$;
5. $0m = 0$;
6. $r0 = 0$.

When $R$ is a ring with identity and $(M, +)$ is an abelian group, conditions 5 and 6 follow from the others: expanding $(0 + 0)m$ by condition 1 and $r(0 + 0)$ by condition 2 and cancelling in $M$ gives $0m = 0$ and $r0 = 0$. In that setting the definition is the usual definition of a left module over a ring with identity, by conditions 1 to 4. Mathlib explicitly includes both zero laws; without additive cancellation, $0_R \cdot m = 0_M$ need not follow from the first four.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004. For modules over a ring with identity.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the conditions $(r + s)m = rm + sm$ and $0m = 0$ of a module over a semiring on a commutative monoid: `Module`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/Defs.lean#L54-L59.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the conditions $r(m + n) = rm + rn$ and $r0 = 0$: `DistribMulAction`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/GroupWithZero/Action/Defs.lean#L346-L350.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the condition $1m = m$: `MulAction`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Action/Defs.lean#L133-L135.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the condition $(rs)m = r(sm)$: `SemigroupAction`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Action/Defs.lean#L102-L104.
