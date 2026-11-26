# Sharp terminal edge count for random triangle removal

Start with $K_n$. At each step choose uniformly among present triangles and delete its three edges; when there is no triangle the state is absorbing. Let $L_n$ be the edge count after $\binom n2$ steps, which is the terminal count. Set $X_n=L_n/n^{3/2}$ and $c=1/(2\sqrt2)$. Then $\mathbb E[(X_n-c)^2]\to0$, for each $\epsilon>0$ one has $\Pr(|X_n-c|>\epsilon)\to0$, and $\mathbb E[L_n]/n^{3/2}\to c$ as $n\to\infty$ through the natural numbers. All expectations are with respect to the finite terminal law.

## Depends on

- Simple labelled graphs, triangle-uniform deletion kernel with absorbing terminal configurations, and finite expected values.

## Proof depends on

- Sharp second-moment estimate for the random leave, then finite-measure deductions of probability and mean convergence.

## Expansion

Prove the deterministic stopping horizon before using the terminal law. Split the process estimate, concentration and expected-count limits. Preserve the $n^{3/2}$ normalization and the constant, not only a growth exponent.

## Sources

- [Comparator statement: `OAI.SharpTerminalLeave.sharp_terminal_leave`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TriangleRemoval.lean#L55-L64)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/188.md)
