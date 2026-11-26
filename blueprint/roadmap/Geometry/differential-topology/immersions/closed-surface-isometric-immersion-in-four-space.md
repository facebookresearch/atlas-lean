# Smooth isometric immersion of a closed surface into Euclidean four-space

Let $M$ be a compact Hausdorff second-countable smooth manifold modeled on $\mathbb R^2$ without boundary, and let $g$ be a smooth positive-definite Riemannian metric on $TM$. There exists a smooth $F:M\to\mathbb R^4$ such that for every $p\in M$ and every $v,w\in T_pM$,

$$\langle dF_p(v),dF_p(w)\rangle_{\mathbb R^4}=g_p(v,w).$$

There is no orientability or connectedness hypothesis. The equality forces the differential to be injective, but the map need not be globally injective.

## Depends on

- [Injective differential and immersions](immersion-at-of-injective-mfderiv.md)
- Smooth Riemannian metric and manifold derivative into Euclidean four-space.

## Proof depends on

- Finite-order construction and smoothing that preserves the metric equation, not merely convergence of approximately isometric immersions.

## Expansion

Reuse the native tangent-bundle metric, isolate the finite-order immersion and smoothing theorem, and check that the metric equation survives uniformly on the whole compact surface.

## Sources

- OpenAI Math, [`smooth_isometric_immersion`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SurfaceImmersion.lean#L39-L43) (statement and local definitions).
