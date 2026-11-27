# A smooth metric on a square with no local isometric immersion in three-space

There exists a matrix field $g:(-1,1)^2\to\mathbb R^{2\times2}$ with smooth entries and positive-definite symmetric values. For every open $U\subseteq(-1,1)^2$ containing the origin, there is no smooth $F:U\to\mathbb R^3$ with

$$\langle dF_p(v),dF_p(w)\rangle_{\mathbb R^3}=v^{\mathsf T}g(p)w\qquad(p\in U,\ v,w\in\mathbb R^2).$$

The same $g$ defeats every neighborhood and every smooth map on that neighborhood.

## Depends on

- [Injective differential and immersions](immersion-at-of-injective-mfderiv.md)
- Open-coordinate domains with restricted metrics, positive-definite matrices and manifold derivatives.

## Proof depends on

- The local obstruction at the origin for the specific smooth positive-definite metric.

## Expansion

Check that the obstructing data are smooth at the origin and form a strictly positive metric. Derive obstruction on each open subdomain without relying on any global injectivity requirement.

## Sources

- OpenAI Math, [`exists_local_metric_without_local_immersion`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/IsometricImmersion.lean#L46-L57) (statement and local definitions).
