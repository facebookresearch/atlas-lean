# Positively curved Einstein four-manifolds without an orientability hypothesis

Write $d_g$ for the intrinsic path distance. Einstein means $\operatorname{Ric}_g=\lambda g$ with a single real constant $\lambda$, and strict sectional positivity is tested on every independent tangent pair. For the round unit $S^4$ use distance $\arccos\langle x,y\rangle$. For the complex Fubini–Study model $\mathbb CP^2$ and round $\mathbb RP^4$, use $\arccos(|\langle z,w\rangle|/(\|z\|\|w\|))$ on nonzero representatives with the Hermitian or real inner product, respectively. A model identification is a bijection identifying its distance with $\sqrt a\,d_g$ for some $a>0$.

Let $M$ be a smooth connected compact Hausdorff second-countable four-manifold without boundary. For every smooth Einstein metric $g$ on $M$ of strictly positive sectional curvature there is such a model identification with $S^4$, $\mathbb CP^2$, or $\mathbb RP^4$. No classification for mere nonnegative sectional curvature is asserted.

## Depends on

- [Einstein metric](is-einstein.md)
- [Sectional curvature](sectional-curvature.md)
- Coordinate Ricci and sectional numerators compared with intrinsic tensors; explicit distances of the model projective spaces.

## Proof depends on

- [Oriented classification](positively-curved-oriented-einstein-four-manifolds.md)
- Pass to an oriented cover and control the free isometric deck actions that can give quotients.

## Expansion

The universally quantified metric and its two hypotheses are the same whether packaged on a fixed $M$ or exposed as binders. Verify the possible quotients of the two oriented models and the corresponding distance formulas.

## Sources

- OpenAI Math, [`classification`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EinsteinFour.lean#L207-L217) (statement and local definitions).
- OpenAI Math, [`classificationOn`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EinsteinFour.lean#L202-L204).
