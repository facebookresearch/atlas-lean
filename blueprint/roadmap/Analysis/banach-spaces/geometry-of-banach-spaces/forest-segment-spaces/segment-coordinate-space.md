# Coordinate space of a segment-norm completion

Let $V$ be a partially ordered set. A segment is a finite chain that is order-convex in $V$: if $a$ and $b$ belong to it and $a\le v\le b$, then it contains $v$. For a finitely supported real vector $u$ on $V$, put

$$\rho(u)=\sqrt{\sup_{(S_i)}\sum_i\biggl(\sum_{v\in S_i}u(v)\biggr)^2},$$

where the supremum is over all finite indexed families of pairwise disjoint segments. Empty segments and the empty family contribute zero terms. Singletons detect the coordinates, and the supremum is bounded by the square of the finite sum of absolute coordinate values. When $V$ is nonempty the norm can equivalently be calculated by taking the supremum of the square roots over positive-size families of nonempty segments.

Let $J(V)$ be the real normed-space completion in $\rho$. Write $e_v\in J(V)$ for the vector equal to $1$ at $v$ and $0$ elsewhere, and $e_v^*\in J(V)^*$ for the continuous extension of evaluation at coordinate $v$. The extension is bounded because the singleton segment gives $|u(v)|\le\rho(u)$. Define

$$X(V)=\overline{\operatorname{span}_{\mathbb R}\{e_v^*:v\in V\}}^{\|\cdot\|}\subseteq J(V)^*,$$

with the operator norm inherited from the real continuous dual. This is the closed coordinate span, not a definition of the full dual and not a reflexivity assumption.

## Depends on

- Finitely supported real vectors, normed-space completion, and the continuous real dual with its operator norm.

## Proof outline

Disjointness makes the sum of the absolute segment sums at most the finite sum of the absolute coordinate values, so the squared tests are bounded. For each family, the Euclidean triangle inequality bounds the test of a sum of vectors by the sum of their norms. Singletons give definiteness and bound evaluation before completion.

## Sources

- OpenAI, [finite order-convex chains and disjoint segment tests](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Segments.lean#L17-L29), [the squared supremum and its nonempty-segment form](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Norm.lean#L16-L28), [equality with the nonempty-segment supremum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Norm.lean#L252-L259).
- OpenAI, [test-vector norm](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Completion.lean#L132-L155), [completed space and full dual](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Completion.lean#L384-L388), [extended evaluations and their closed span](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Polar.lean#L172-L207).
