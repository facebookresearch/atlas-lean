# Gromov width of symmetric polar products

For $n\geq2$ let $K\subset\mathbb R^n$ be compact, convex, origin-symmetric, with nonempty interior, and put $K^\circ=\{p:q\cdot p\leq1\text{ for all }q\in K\}$. On $\mathbb R^n\times\mathbb R^n$ take $\omega_0((q,p),(q',p'))=q\cdot p'-q'\cdot p$. Let $B_c=\{(q,p):\pi(|q|^2+|p|^2)<c\}$. An embedding is a smooth map on $B_c$, topologically embedded into the target, preserving $\omega_0$ by its derivative at every point. The supremum of positive $c$ for which $B_c$ embeds in $\operatorname{int}K\times\operatorname{int}K^\circ$ is $4$; every $0<c<4$ admits such an embedding. The claim makes no assertion at $c=4$.

## Depends on
The standard symplectic form, open capacity ball and smooth topological embedding, and the interiors of the body and its polar.

## Proof depends on
A capacity obstruction for $c>4$ and a matching embedding construction from a nonsmooth symmetric body and its polar.

## Expansion
State non-squeezing or the suitable capacity bound in this normalization, construct the subcritical embeddings first for the smooth model, and justify extension by approximation without asserting that the supremum is attained.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SymmetricPolar.lean#L40-L46) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/087.md).
