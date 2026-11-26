# Midpoint-lens tail estimate in a forest dual and an infinite-tree coordinate span

Use two ancestral orders: the disjoint union of trees of words of length at most $h$ over $\mathbb N$ for all $h\ge1$, and the tree of all finite words over $\mathbb N$. In each tree ancestry is prefix order, including the empty root. Give finitely supported real coordinates the supremum of $(\sum_i|\sum_{s\in S_i}a_s|^2)^{1/2}$ over finite disjoint families of nonempty finite ancestral intervals and complete. In the forest use the full continuous dual; in the infinite tree use the norm-closed span of the coordinate functionals in the continuous dual.

In either of the resulting spaces, let $H$ be a finite set closed under ancestors, $P_Hx=\sum_{v\in H}x(e_v)e_v^*$ the finite-head projection, $x=P_Hx$, and $R\ge0$. If $\|x+y\|,\|x-y\|\le R$, then $\|y-P_Hy\|\le2\sqrt{R^2-\|x\|^2}$, with tail norm in the ambient dual. The bounds imply $\|x\|\le R$.

## Depends on

- The interval segment norm, dual coordinate extensions and finite-head projection above.

## Proof depends on

- Decomposition of segment tests across an ancestral head and a dual midpoint-lens estimate for the two indicated spaces.

## Expansion

Construct the finite-head and tail maps through completion and distinguish the full dual from the closed coordinate span. Establish the lens estimate for admissible test decompositions before applying it to the two models.

## Sources

- OpenAI, [MidpointLenses comparator, midpoint_lens_main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MidpointLenses.lean#L328-L338).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
