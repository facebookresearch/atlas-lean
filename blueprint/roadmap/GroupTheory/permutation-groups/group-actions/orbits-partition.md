# The orbits of a group action partition the set acted on

Let a group $G$ act on a set $X$, and for $x \in X$ let $G \cdot x = \{g \cdot x : g \in G\}$ be the orbit of $x$. The orbits form a partition of $X$: no orbit is empty, and every element of $X$ lies in exactly one orbit. In particular, any two orbits are either equal or disjoint.

## Sources

- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004, §4.1, Proposition 2, p. 114, and the remark following its proof, p. 115, for a nonempty set acted on.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the meaning of a partition, whose blocks are nonempty: `Setoid.IsPartition`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Setoid/Partition.lean#L192-L194.
