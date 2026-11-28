# Isoperimetric minimizers of the unit cubic three-torus

On $\mathbb R^3/\mathbb Z^3$ with its unit cubic flat metric, use volume pushed forward from $[0,1)^3$. The perimeter of $E$ is the supremum of $\int_E\operatorname{div} X$ over smooth periodic vector fields of pointwise norm at most one, allowing $+\infty$. Minimize over null-measurable sets of finite perimeter and volume $V$.

For every $0<V<1$ a minimizer exists, every minimizer has perimeter

$$\min\{(36\pi)^{1/3}v^{2/3},\ 2\sqrt{\pi v},\ 2\},\qquad v=\min(V,1-V),$$

and a set is a minimizer exactly when, modulo a flat isometry and a null set, it has one of the following shapes at volume $v$ (take its complement if $V>1/2$): a ball of radius $(3v/(4\pi))^{1/3}$ for $v\le4\pi/81$; a circular tube of radius $\sqrt{v/\pi}$ along a coordinate shortest closed geodesic for $4\pi/81\le v\le1/\pi$; or a coordinate slab of width $v$ for $v\ge1/\pi$. Both adjacent shapes occur at each transition, and no endpoint $V=0$ or $1$ is claimed.

## Depends on

- [Riemannian volume](riemannian-volume.md)
- Flat torus metric and volume, null-measurability, divergence perimeter and congruence modulo null sets.

## Proof depends on

- Existence, sharp lower bounds in all ranges, exact perimeter evaluations and rigidity including both ties.

## Expansion

Use a common finite-perimeter model for the lower bound and equality cases. Split volume/perimeter evaluation of standard regions from compactness and the classification of all possible minimizers.

## Sources

- OpenAI Math, [`unit_cubic_isoperimetric`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CubicTorus.lean#L87-L94) (statement and local definitions).
