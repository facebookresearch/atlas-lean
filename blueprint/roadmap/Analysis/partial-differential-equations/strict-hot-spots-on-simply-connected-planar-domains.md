# Strict interior hot-spots bound on smooth simply connected planar domains

Let $\Omega\subset\mathbb R^2$ be nonempty, open, bounded and simply connected. At each boundary point require an open neighborhood on which a smooth defining function vanishes at the point, has nonzero derivative there and cuts out $\Omega$ by its strict negative sublevel. For $H^1(\Omega)$ use square-integrable functions with square-integrable weak gradient, tested against compactly supported smooth functions in every constant direction. Let $\lambda$ be the infimum of $\int_\Omega\|\nabla v\|^2/\int_\Omega v^2$ over mean-zero $H^1$ functions with positive denominator.

Suppose $u$ is smooth on the closure, $(u,\nabla u)$ satisfies the $H^1$ condition, $\int_\Omega u=0$, and $\int_\Omega\langle\nabla u,\nabla v\rangle=\lambda\int_\Omega uv$ for every $H^1$ test $v$ (not just mean-zero tests). If $u$ is nonzero at some interior point, then at every interior point $x$,

$$\nabla u(x)\ne0,\qquad \inf_{\partial\Omega}u < u(x) < \sup_{\partial\Omega}u.$$

The assertion does not assume simplicity of the eigenvalue.

## Depends on

- The weak-gradient Neumann eigenspace and its Rayleigh quotient above.

## Proof depends on

- Boundary regularity and the exclusion of interior critical points for every first-eigenspace nonzero vector, including when the eigenspace is not one-dimensional.

## Expansion

Match the smooth-boundary/Rayleigh model to a Neumann spectral API. Isolate the interior critical-point exclusion under simple connectedness, then deduce the strict boundary range inequalities from attainment on the compact closure.

## Sources

- OpenAI, [HotSpots comparator, main_theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HotSpots.lean#L49-L53).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/369.md).
