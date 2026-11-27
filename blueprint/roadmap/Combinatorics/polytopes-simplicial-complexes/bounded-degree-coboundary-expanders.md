# Bounded-degree coboundary expanders over F₂ in dimensions at least three

For each $d\ge3$ there are $D\in\mathbb N$, $\epsilon>0$ and a sequence of finite abstract simplicial complexes $X_m$ on labelled vertices containing all singletons and the empty face. Each has connected nonempty 1-skeleton and is pure of dimension $d$: top faces exist and contain every face. Vertex counts tend to infinity, and each vertex is in at most $D$ top faces. For $i<d$ and every $\mathbb F_2$-valued $i$-cochain $f$,

$$
\epsilon\min_{b\in B^i}\|f-b\|_i\le\|\delta_i f\|_{i+1}.
$$

The coboundary sums values on codimension-one subfaces modulo two. Here $B^0$ consists of constants and $B^{i+1}=\mathrm{im}(\delta_i)$. The weighted support norm in degree $i$ sums, over nonzero faces, their count of containing top faces divided by $\binom{d+1}{i+1}$ times the number of top faces (the binomial coefficient and number of top faces are both in the denominator).

## Depends on

- Finite pure complexes, normalized weighted support norms, simplicial F₂ coboundary and distance to the coboundary subspace.

## Proof depends on

- Explicit pure connected family of unbounded vertex count, uniform top incidence, and expansion in all degrees below d.

## Expansion

Supply a bridge from the combinatorial face interface to reduced cochains (constant degree-zero boundaries). Separate bounded vertex incidence and growth from the inequality proof, keeping a common epsilon for all degrees. No dimension-one or dimension-two claim is included.

## Sources

- [Comparator statement: `OAI.CoboundaryExpanders.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoboundaryExpanders.lean#L91-L93)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/177.md)
