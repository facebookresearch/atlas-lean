# Action of a monoid or a group on a set

Let $M$ be a monoid with identity $1$, for instance a group $G$, and let $A$ be a set. A *(left) action* of $M$ on $A$ is a map $M \times A \to A$, written $(g, a) \mapsto g \cdot a$, such that $g_1 \cdot (g_2 \cdot a) = (g_1 g_2) \cdot a$ for all $g_1, g_2 \in M$ and $a \in A$, and $1 \cdot a = a$ for all $a \in A$. The action is on the left: the product $g_1 g_2$ acts by applying $g_2$ first and then $g_1$. When $M = G$ is a group, this is the usual notion of an action of $G$ on $A$, and each map $a \mapsto g \cdot a$ is a bijection of $A$, with inverse $a \mapsto g^{-1} \cdot a$, since $g^{-1} \cdot (g \cdot a) = (g^{-1} g) \cdot a = 1 \cdot a = a$ and likewise $g \cdot (g^{-1} \cdot a) = a$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for actions of a monoid, with the condition $1 \cdot a = a$: `MulAction`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Action/Defs.lean#L120-L135.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the left-action condition $(g_1 g_2) \cdot a = g_1 \cdot (g_2 \cdot a)$: `SemigroupAction`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Group/Action/Defs.lean#L102-L104.
