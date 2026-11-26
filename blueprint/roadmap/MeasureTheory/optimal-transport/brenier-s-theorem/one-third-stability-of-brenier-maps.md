# One-third stability of Brenier maps

Let $d\ge2$ and let $S\subset\mathbb R^d$ be compact, convex and have nonempty interior. Let $K\subset\mathbb R^d$ be compact and nonempty and put $\sigma=\operatorname{vol}(S)^{-1}\operatorname{vol}|_S$. There exists $C\ge0$ depending on $d,S,K$ but not on the targets, such that for every pair of probability measures $\mu,\nu$ giving full mass to $K$ there are Borel transports $T_\mu,T_\nu$ from $\sigma$ to the respective targets. Each graph plan $(\mathrm{id},T)_\#\sigma$ minimizes $\int\|x-y\|^2\,d\pi$ over all corresponding probability couplings and is the unique minimizing plan. Then

$$\left(\int\|T_\mu-T_\nu\|^2\,d\sigma\right)^{1/2}\le C\,W_2(\mu,\nu)^{1/3},$$

where $W_2$ is the square root of the infimum of the quadratic cost over couplings of the targets. Uniqueness of plans is not pointwise uniqueness of Borel representatives.

## Depends on

- [Wasserstein distance](../wasserstein-distances/wasserstein-distance/wasserstein.md), in the finite-cost quadratic specialization.

## Proof depends on

- [Brenier's theorem](brenier.md).
- The quantitative quadratic transport comparison for arbitrary compactly supported targets with a common bound.

## Expansion

Bridge the finite-cost coupling and graph-plan definitions, prove the uniform map-defect estimate independently of the pair of target measures, and combine it with existence and uniqueness of quadratic optimal plans. No regularity of the targets or strict convexity of $S$ is assumed.

## Sources

- OpenAI, [Brenier comparator, one_third_stability](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brenier.lean#L73-L87).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/374.md).
