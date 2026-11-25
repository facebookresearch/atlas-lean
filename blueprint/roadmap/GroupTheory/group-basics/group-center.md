# Center of a group

Let $G$ be a group. The *center* $Z(G)$ of $G$ is the subgroup of $G$ made up of the elements $z \in G$ such that $zg = gz$, $z(gh) = (zg)h$ and $(gh)z = g(hz)$ for all $g, h \in G$. The last two conditions hold for every $z$ by associativity, so $Z(G) = \{z \in G : zg = gz \text{ for all } g \in G\}$ is the set of elements of $G$ that commute with every element of $G$.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004, §2.2, p. 50.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the defining conditions of a central element: `IsMulCentral`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Group/Center.lean#L58-L66.
