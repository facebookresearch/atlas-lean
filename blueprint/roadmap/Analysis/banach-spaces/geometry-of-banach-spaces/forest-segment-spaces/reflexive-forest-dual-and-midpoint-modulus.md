# Reflexive forest dual with a midpoint modulus and no AUC norm

Use the forest that is the disjoint union, for $h\ge1$, of trees of words over $\mathbb N$ of length at most $h$, ordered by prefix only within a fixed component. Complete its finitely supported real sequences in the supremum norm over finite disjoint families of finite order-convex chains, a family contributing $(\sum_i|\sum_{v\in S_i}a_v|^2)^{1/2}$. The full continuous real dual $X$ of that completion is infinite-dimensional, separable and canonically reflexive (onto its bidual by the evaluation map).

For every $t>0$ the averaged modulus $\inf_{\|x\|=1}\sup_F\inf_{y\in F,\|y\|=1}[(\|x+ty\|+\|x-ty\|)/2-1]$ is at least $\sqrt{1+t^2/12}-1$, with $F$ norm-closed finite codimensional. For every seminorm $N$ and $0<\alpha\le\beta$ with $\alpha\|x\|\le N(x)\le\beta\|x\|$, the one-sided modulus defined by replacing the norm by $N$ and the average by $N(x+ty)-1$ fails to be positive for all $t>0$.

Start a graph at a single edge, and for $k$ rounds replace each edge by countably many two-edge paths with distinct midpoint vertices. On the final graph use unweighted shortest-path distance $d_k$. If $f$ maps its vertices to $X$ and for some $s>0$ all pairs satisfy $s d_k(u,v)\le\|f(u)-f(v)\|\le C s d_k(u,v)$, then $\sqrt{1+k/12}\le C$.

## Depends on

- Ancestral segment-norm completion, its full continuous dual and the countably branching diamond distance.

## Proof depends on

- Reflexivity and separable-dual structure, finite-head estimates for the unit-direction modulus, obstruction for arbitrary equivalent norms, and the diamond iteration at coefficient $1/12$.

## Expansion

Separate the construction, positive modulus, renorming and graph conclusions. Show that the dual, not merely the coordinate span, satisfies all the conclusions. This endpoint does not use directions of norm merely at least one in its modulus definition.

## Sources

- OpenAI, [ForestSpace comparator, main_theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ForestSpace.lean#L450-L463).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
