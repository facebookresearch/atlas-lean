# Oriented positively curved Einstein four-manifolds

Write $d_g$ for the intrinsic path distance. Einstein means $\operatorname{Ric}_g=\lambda g$ with a single real constant $\lambda$, and strict sectional positivity is tested on every independent tangent pair. For the round unit $S^4$ use distance $\arccos\langle x,y\rangle$. For the complex Fubini–Study model $\mathbb CP^2$ and round $\mathbb RP^4$, use $\arccos(|\langle z,w\rangle|/(\|z\|\|w\|))$ on nonzero representatives with the Hermitian or real inner product, respectively. A model identification is a bijection identifying its distance with $\sqrt a\,d_g$ for some $a>0$.

If $(M,g)$ is a smooth connected compact oriented Riemannian four-manifold without boundary and $g$ is Einstein with strictly positive sectional curvature, then it admits such a model identification with $S^4$ or $\mathbb CP^2$. In the source an orientation is a clopen positive choice on orthonormal frames, meeting every fibre and separating determinant signs.

## Depends on

- [Einstein metric](is-einstein.md)
- [Sectional curvature](sectional-curvature.md)
- Coordinate Ricci and sectional numerators compared with intrinsic tensors; explicit distances of the model projective spaces.
- Oriented orthonormal frame bundles.

## Proof depends on

- Classify the oriented case using the curvature rigidity in dimension four.

## Expansion

Transport the source frame orientation and verify the chart formulas’ signs for the native curvature. Prove the rigidity before identifying the metric distances.

## Sources

- OpenAI Math, [`orientedClassification`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EinsteinFour.lean#L189-L195) (statement and local definitions).
