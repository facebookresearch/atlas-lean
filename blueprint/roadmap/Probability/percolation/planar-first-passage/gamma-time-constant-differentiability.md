# Differentiability of the planar Gamma first-passage norm

On any probability space, give each unoriented nearest-neighbor edge of $\mathbb Z^2$ an independent measurable passage time with Gamma law of shape $a>0$ and rate $b>0$. An unoriented edge is indexed by its lower endpoint and one of the two positive coordinate directions. For a finite nearest-neighbor walk, sum the traversed edge weights with multiplicity; let $T(x,y)$ be the infimum of these sums over walks from $x$ to $y$ (allowing the empty walk).

There exists a deterministic norm $\mu$ on $\mathbb R^2$ such that for each fixed $v$, almost surely $T(0,\lfloor tv\rfloor)/t\to\mu(v)$ as real $t\to+\infty$, with coordinatewise floor. The norm is Fréchet differentiable at every nonzero $v$. For each point of $S=\partial\{z:\mu(z)\le1\}$, there is an open neighborhood $U$ and a $C^1$ curve $\gamma:\mathbb R\to S\cap U$ with nonzero derivative everywhere and an inverse given by a function $\theta:\mathbb R^2\to\mathbb R$ continuous on $U$: $\theta(\gamma(t))=t$ for all $t$, and $\gamma(\theta(z))=z$ on $S\cap U$.

**Conventions.** Use the unoriented passage-time metric built from the edge law and the pointwise directional limit after coordinatewise rounding. A boundary chart here gives a nondegenerate local parametrization with its continuous inverse, not just a measurable parametrization.

## Depends on

- [Planar first-passage metric and time constant](planar-passage-time-and-time-constant.md)

## Proof depends on

Existence and nondegeneracy of the deterministic Gamma time constant, the planar no-corner estimate, and a convex-geometric passage from differentiability to regular local boundary charts.

## Expansion

Separate the shape-theorem and differentiability steps. Prove the hypotheses of the Gamma no-corner estimate for all positive shapes, including shapes below $1$ where the density diverges at zero. Construct inverse charts from the unit norm level set. Do not infer strict convexity.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GammaPassage.lean#L107-L109)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/212.md)
- [Accompanying manuscript: Strict convexity and differentiability of the planar exponential first-passage limit shape](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf)
