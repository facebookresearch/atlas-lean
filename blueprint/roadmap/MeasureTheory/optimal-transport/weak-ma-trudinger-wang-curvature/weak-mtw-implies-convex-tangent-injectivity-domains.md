# Convexity of tangent injectivity domains under weak MTW

Let $M$ be a compact connected smooth Riemannian manifold without boundary of dimension $n\ge2$, with its Riemannian distance. Use the cost $c(x,y)=d(x,y)^2/2$. For $x\in M$ define $I_x=\{v\in T_xM:\exists a>1,\ d(x,\exp_x(av))=a\|v\|\}$. Here the source chooses a time-one endpoint of a smooth complete geodesic with the prescribed base point and initial velocity, locally minimizing at constant speed $\|v\|$; if no such geodesic exists, the totalized endpoint is $x$. Identification with the native exponential requires existence and uniqueness for these initial data. Weak MTW means that, for every $x$, $v\in I_x$, and $\xi,\eta\in T_xM$ with $\langle\xi,\eta\rangle=0$,

$$-\tfrac32\partial_s^2\partial_t^2 c(\exp_x(t\xi),\exp_x(v+s\eta))\big|_{s=t=0}\ge0.$$

If weak MTW holds then $I_x$ is linearly convex in $T_xM$ for every $x$. There is no prior convexity or nonfocality assumption. No separate global support or arbitrary-potential injectivity theorem is part of this endpoint.

## Depends on

- Complete exponential map, open tangent injectivity domain, squared-distance cost, mixed fourth derivative off the cut locus.

## Proof depends on

- Bridge the chosen exponential endpoint to the native initial-value predicate and establish the weak-MTW convexity argument at all base points.

## Expansion

Prove the directional extendible-minimizer definition matches the native Riemannian domain (not the radius ball), including agreement of exponential maps and distances. Keep the convexity assertion independent of later transport claims.

## Sources

- OpenAI Math, [`current_main_convexity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeakMTWGlobalSupport.lean#L62-L76) (statement and local definitions).
- OpenAI Math, [totalized geodesic endpoint, injectivity domain, and weak MTW test](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeakMTWGlobalSupport.lean#L21-L54).
