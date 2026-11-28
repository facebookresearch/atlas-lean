# Uniform rarity of large pinned distance fibers

Let $s>0$. For a finite set $P\subset\mathbb R^2$ and distinct $x,y\in P$, let $k_P(x,y)=\#\{z\in P\setminus\{x\}:d(z,x)=d(y,x)\}$. For $n\ge2$, take the supremum over $|P|=n$ of the number of **ordered** distinct pairs satisfying $k_P(x,y)\ge n^s$, divided by $n(n-1)$. Put this supremum equal to zero for $n=0,1$. It tends to zero as $n\to\infty$ for every fixed $s>0$. This endpoint asserts the large-fiber limit, not a separate quantitative bound on the number of pins with few distances.

## Depends on

- [Distinct distances from a pin](distinct-distances-from.md)
- Pinned distance fibers counted away from the pin, and the finite-set normalized supremum.

## Proof depends on

- Uniform avoidance of a positive-density family of large fibers in the planar distance profiles.

## Expansion

Extend the existing distance-count model by fiber at a single pin, not by global distance multiplicity. Prove the boundedness of the normalized supremum and decompose the source’s compactness and overlap argument.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PinnedDistances.lean#L29-L31) (statement and local definitions).
