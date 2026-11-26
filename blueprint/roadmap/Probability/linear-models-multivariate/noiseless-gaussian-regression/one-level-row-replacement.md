# One-level replacement with an explicit message-entropy penalty

In the [exposed-information experiment](conditional-information-from-marginal-kernels.md), now let the message space be finite with measurable singletons and let $X$ have $\lfloor d/32\rfloor$ rows. Its joint marginal with $S$ is again uniform sphere times the standard Gaussian array law. In the actual experiment append independent rows to width $\lfloor d/4\rfloor$, and in the fresh experiment replace every row at that width by an independent Gaussian array. There are absolute $C>0,d_0$ such that for every $d\ge d_0$ and every such law, the fresh exposed information is at most the actual exposed information plus

$$
C\big[d+\log(1+d+H(W))+H(W)/d\big].
$$

There is no $H(W)\le d^2$ assumption at this endpoint.

**Conventions.** Use the same exact labels, conditional KL and finite message entropy, with the one-level width and the explicit real entropy penalty.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

A one-level replacement comparison uniform over all finite message laws, with control of each term in the entropy penalty.

## Expansion

Separate the fixed geometric and entropy-dependent error terms. Do not substitute the $O(d)$ bound for the critical entropy-restricted model unless an additional entropy bound is actually assumed.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L505-L507)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
