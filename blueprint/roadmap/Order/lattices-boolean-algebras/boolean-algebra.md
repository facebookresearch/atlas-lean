# Boolean algebra

A *Boolean algebra* is a distributive lattice $(B, \le)$, with join $\vee$ and meet $\wedge$, together with a greatest element $\top$, a least element $\bot$, a complement operation $x \mapsto x'$, a difference operation $(x, y) \mapsto x \setminus y$ and an implication operation $(x, y) \mapsto (x \Rightarrow y)$, such that for all $x, y \in B$:

- $x \wedge x' \le \bot$ and $\top \le x \vee x'$, so that $x \wedge x' = \bot$ and $x \vee x' = \top$;
- $x \setminus y = x \wedge y'$ and $(x \Rightarrow y) = y \vee x'$.

Here distributive means that $(x \vee y) \wedge (x \vee z) \le x \vee (y \wedge z)$ for all $x, y, z \in B$. The difference and implication operations are determined by the lattice operations and the complement; the usual signature $(B; \vee, \wedge, {}', 0, 1)$ of a Boolean algebra, with $0 = \bot$ and $1 = \top$, does not include them.

## Sources

- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the difference and implication operations and their two equations: `BooleanAlgebra`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/BooleanAlgebra/Defs.lean#L101-L118.
