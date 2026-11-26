# Uniform bi-Hölder optimal transport under weak MTW

Let $M$ be a compact connected smooth Riemannian manifold without boundary of dimension $n\ge2$, with its Riemannian distance. Use the cost $c(x,y)=d(x,y)^2/2$. For $x\in M$ define $I_x=\{v\in T_xM:\exists a>1,\ d(x,\exp_x(av))=a\|v\|\}$. Here the source chooses a time-one endpoint of a smooth complete geodesic with the prescribed base point and initial velocity, locally minimizing at constant speed $\|v\|$; if no such geodesic exists, the totalized endpoint is $x$. Identification with the native exponential requires existence and uniqueness for these initial data. Weak MTW means that, for every $x$, $v\in I_x$, and $\xi,\eta\in T_xM$ with $\langle\xi,\eta\rangle=0$,

$$-\tfrac32\partial_s^2\partial_t^2 c(\exp_x(t\xi),\exp_x(v+s\eta))\big|_{s=t=0}\ge0.$$

Use the $n$-dimensional Hausdorff volume normalized to agree with Euclidean Lebesgue volume. Fix real bounds $0<\ell\le h$ such that the admissible density class is nonempty, where admissibility is a.e. measurability, integrability with integral one, and $\ell\le\rho\le h$ a.e. There are $0<\alpha\le1$, $C\ge0$ such that for every pair of admissible densities $\rho_0,\rho_1$ there is a homeomorphism $T:M\to M$ carrying $\rho_0\,d\mathrm{vol}$ to $\rho_1\,d\mathrm{vol}$ and minimizing $\int c(x,T(x))\rho_0(x)\,d\mathrm{vol}(x)$ among all measurable maps with that pushforward. Every optimal map equals $T$ almost everywhere for the source measure. Both $T$ and $T^{-1}$ are globally Hölder with the **same** exponent $\alpha$ and constant $C$, which are fixed before choosing the pair on this manifold.

## Depends on

- [Riemannian volume](../../../Geometry/riemannian-geometry/riemannian-volume/riemannian-volume.md)
- Weak MTW and exponential-domain comparison, intrinsic Riemannian volume normalization, Monge maps and source-measure uniqueness.

## Proof depends on

- [Convexity of injectivity domains](weak-mtw-implies-convex-tangent-injectivity-domains.md)
- Uniform regularity for maps in both directions on the whole manifold; estimates with constants independent of the density pair.

## Expansion

Extend the same weak-MTW model as in the convexity question. Decompose existence, uniqueness a.e., and uniform forward/inverse Hölder estimates; show the two continuous representatives are inverse everywhere.

## Sources

- OpenAI Math, [`uniform_biHolder_transport`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BiholderTransport.lean#L98-L122) (statement and local definitions).
- OpenAI Math, [totalized geodesic endpoint, injectivity domain, and weak MTW test](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BiholderTransport.lean#L59-L93).
