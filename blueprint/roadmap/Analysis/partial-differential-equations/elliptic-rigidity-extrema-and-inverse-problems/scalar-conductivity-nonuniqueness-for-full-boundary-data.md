# Scalar conductivity nonuniqueness for full weak boundary data

Let $D=B(0,3)\subset\mathbb R^3$. Let $H^1$ be the closure of the linear span of smooth jets $(u,\nabla u)$ in $L^2(D;\mathbb R^4)$, and let $H^1_0$ consist of jets in $H^1$ lying in the closure of the span of jets of smooth functions compactly supported inside $D$. Write $Q=H^1/H^1_0$ and $[v]$ for a trace. The second through fourth coordinates of a jet give its weak gradient. Given $\gamma$, put $a_\gamma(u,v)=\int_D\gamma\langle\nabla u,\nabla v\rangle$. The Dirichlet-to-Neumann map is the bounded linear map $\Lambda:Q\to Q^*$ such that for each $f\in Q$ there is a unique $u$ with $[u]=f$ and $a_\gamma(u,h)=0$ for all $h\in H^1_0$, and $(\Lambda f)([v])=a_\gamma(u,v)$ for all $v\in H^1$.

There exist measurable, essentially bounded real scalar conductivities $\gamma_0,\gamma_1$ and common real bounds $0<c<C$ such that $c\le\gamma_i\le C$ almost everywhere in $D$. For each $i$ there is $0<r_i<3$ with $\gamma_i=1$ almost everywhere on $r_i<\|x\|<3$. They differ on a set of positive Lebesgue measure in $D$ and admit one and the same $\Lambda$ on the full quotient $Q$. This is not a recovery statement about a metric and a connection, or data restricted to a boundary patch.

## Depends on

- The closed jet spaces, quotient trace and bounded energy pairing above.

## Proof depends on

- Coercive unique solvability on zero traces and the construction of distinct, uniformly elliptic scalar coefficients with identical boundary forms.

## Expansion

Bridge the concrete jet quotient to the weak trace model, prove the unique minimizer/energy characterization for every trace, and isolate the coefficient construction with positivity, boundary collar and positive-volume distinctness. The common boundary operator must be proved on all traces.

## Sources

- OpenAI, [Conductivity comparator, main_nonuniqueness](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Conductivity.lean#L77-L79).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/365.md).
