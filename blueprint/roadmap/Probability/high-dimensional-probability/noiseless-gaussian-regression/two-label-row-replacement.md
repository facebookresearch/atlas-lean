# The two-label Gaussian replacement estimate

Use the [exposed-information experiment](conditional-information-from-marginal-kernels.md) with a finite singleton-measurable message space and entropy $H(W)\le d^2$. The original row count is $\lfloor d/8\rfloor$, with the independent uniform-sphere and Gaussian $(S,X)$ marginal. Compare the actual array formed by independently appending rows to width $\lfloor d/2\rfloor$ with an entirely fresh independent array of that width. For absolute $C>0,d_0$ and all $d\ge d_0$, the fresh exposed information $I(S;W\mid G,GS)$ is at most the actual exposed information plus $Cd$.

**Conventions.** Use the same exposed-law KL and exact projections, with the specified finite message and entropy hypotheses and the changed original width.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

A replacement argument for this two-label width and information scale; the $d/10$ version with a different row budget is not the same claim.

## Expansion

Identify the two-label comparison and preserve the joint law of the original rows, signal and message until the fresh replacement step. Show the error bound under $H(W)\le d^2$ for the precise width split.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L508-L510)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
