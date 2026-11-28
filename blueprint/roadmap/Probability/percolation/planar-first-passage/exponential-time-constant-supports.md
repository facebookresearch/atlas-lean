# Regularity and unique supports in planar exponential first passage

Give the unoriented nearest-neighbor edges of $\mathbb Z^2$ independent measurable exponential passage times of rate $1$ on a probability space. Let $T$ be the path-sum infimum over finite nearest-neighbor walks. There is a deterministic norm $\mu$ such that for each fixed $v\in\mathbb R^2$, almost surely $T(0,\lfloor tv\rfloor)/t\to\mu(v)$ as real $t\to\infty$, with coordinatewise floor. The norm is Fréchet differentiable off zero.

For every $v$ with $\mu(v)=1$, there is a unique continuous linear $\ell$ satisfying $\ell(v)=1$ and $\ell(w)\le\mu(w)$ for all $w$. Locally the unit sphere is the zero set of a $C^1$ real function with nonzero derivative on its zero set. At each point $v$ of the boundary of $B=\{\mu\le1\}$, there is a unique set $L$ of the form $\{z:g(z)=g(v)\}$ for a nonzero continuous linear $g$ with $g(z)\le g(v)$ throughout $B$. At every such point there is also a regular $C^1$ curve from all of $\mathbb R$ onto $\partial B\cap U$ for some open $U\ni v$, with nowhere-zero derivative and inverse extending to a continuous function on $U$.

**Conventions.** Use the [planar passage-time construction](planar-passage-time-and-time-constant.md) with the exponential law. Normalized supports and supporting lines are different objects.

## Depends on

- [Planar first-passage metric and time constant](planar-passage-time-and-time-constant.md)

## Proof depends on

- [Differentiability of the planar Gamma first-passage norm](gamma-time-constant-differentiability.md)

## Proof outline

Identify the rate-one exponential law with Gamma shape and rate both one and apply the linked planar theorem. Obtain the unique normalized support from the derivative of the norm; identify its supporting line as a set. Use continuity of the derivative of a differentiable convex norm away from zero and its nonzero radial derivative on the unit level to give a local regular defining function. Use the linked boundary chart; do not infer strict convexity.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarFirstPassage.lean#L91-L99)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/212.md)
- [Accompanying manuscript: Strict convexity and differentiability of the planar exponential first-passage limit shape](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf)
