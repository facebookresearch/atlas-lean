# Global bounds for positive weakly reversible mass-action trajectories

For $d>0$ let the finite set of complexes lie in $\mathbb N^d$ and let reactions be a finite set of ordered pairs of distinct complexes. Suppose each reaction $y\to z$ has a directed nonempty return path from $z$ to $y$, and every constant rate $\kappa_{y,z}$ is positive. Set $F(x)=\sum_{y\to z}\kappa_{y,z}(\prod_i x_i^{y_i})(z-y)$, with ordinary integer powers including $x_i^0=1$. For each initial $x^0$ with all coordinates positive there is $0<\epsilon<1$ such that a global forward solution exists, and every global forward solution starting at $x^0$ has $\epsilon\leq x_i(t)\leq\epsilon^{-1}$ for all $t\geq0$ and every $i$. A solution is a map on the real line with $x(0)=x^0$ and derivative $F(x(t))$ at every $t\geq0$, including $t=0$. The bound can depend on this initial point; there is no single absorbing set for an entire compatibility class in this statement.

## Depends on
- [Weak reversibility](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md), with a comparison between finite complexes and return paths in the reaction model.
- [Mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md), with rate exponents equal to the source stoichiometries.

## Proof depends on
The trajectory confinement argument giving both finite upper and positive lower concentration bounds, and continuation of bounded solutions of the polynomial field.

## Expansion
Bridge finite reaction graphs and their real vector fields, separate forward existence/continuation from the invariant concentration bounds, and prove the same box controls all solutions from the fixed positive state. Do not infer classwise absorbing permanence or variable-rate statements.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MassAction.lean#L46-L55) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/149.md).
