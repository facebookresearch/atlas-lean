# The exact two-point law on Gaussian observation fibers

Let $1\le k<d-1$. Draw an independent uniform unit signal $S$ and $k$ standard Gaussian rows $G$. Let $D_0(\sigma_d;G,GS)$ be the [exact density](gaussian-projection-density-model.md) for the uniform sphere, and use the conditional sphere law given $(G,GS)$ to draw a second signal $S'$. Weight this joint measure by $D_0(\sigma_d;G,GS)$ and keep $(G,S,S')$. The result is a finite measure and equals the following finite measure: take two independent uniform sphere points $s,s'$, weight this pair by $(2\pi)^{-k/2}\|s-s'\|^{-k}$, and given the pair draw $k$ independent standard Gaussian rows orthogonally projected onto the hyperplane $(s-s')^\perp$. The source projection formula subtracts $v\langle v,g\rangle/\|v\|^2$ with real division, for $v=s-s'$; on the zero difference it acts as the identity, and the reciprocal weight uses the extended inverse.

**Conventions.** Use the full conditional sphere kernel of the row-label observation and the independent-pair Gaussian hyperplane law, with a weighted finite measure rather than a normalized posterior pair probability on either side.

## Depends on

- [Mixed Gaussian moments of smoothed and exact projection densities](mixed-projection-density-moments.md)

- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof outline

A coarea/disintegration identity for equality of exact labels and the Gaussian density at zero on the difference direction, plus integrability of the singular distance weight.

Prove the identity by integrating against test functions of all three retained coordinates. Check the normalizing power $(2\pi)^{-k/2}$ and integrability up to $k=d-2$; a single diagonal convention must not contribute a positive point mass.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L514-L516)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
