# Actual-row density bounds with conditional row information

Take exactly the [actual-row hypotheses and smoothed and exact densities](actual-row-smoothed-and-exact-bounds.md): $(S,X)\sim\nu\otimes\gamma_m$, finite message entropy, the domination $\nu\le\max(H,0)\sigma_d$, arbitrary finite absolutely continuous selected $\rho_w$ with the two growth bounds, the integrable $g(w)$, the stipulated zero measure and $B_w=D_w=1$ on zero-mass messages, and prefixed dimensions $m,r,q\ge1$, $m+r<d-1$, $r\ge q$. Here define the row information instead as $I=I(X;W\mid S)$, the KL of the law of $(S,X,W)$ against the common law of $S$ times the product of the two conditional marginals given $S$. It is finite and at most $H(W)$.

With independent appended $Z$, $G=(X,Z)$, $Y=GS$ and $A_\delta,A_0$ as before, the conditional label law given $(G,W)$ is almost everywhere absolutely continuous and $A_{1/j}\to A_0$ almost surely. For all $\delta>0$ and for $A_0$, $\log(1+A_\delta)$ with real projection is integrable with expectation at most $I/q+\mathbb E g(W)\le H(W)/q+\mathbb E g(W)$. The positive log part of $A_0$ is integrable and its extended log expectation is bounded by the same $I/q+\mathbb E g(W)$, with infinite negative log part at zero.

**Conventions.** Use the actual-row experiment and the *conditional* KL product-reference law; in particular the countable message has its singleton-measurable structure and the conditionals use standard Borel row and message spaces.

## Depends on

- [Smoothed and exact Gaussian density bounds with actual rows](actual-row-smoothed-and-exact-bounds.md)

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

- [The corresponding product-reference KL result](actual-row-smoothed-and-exact-bounds.md)

The stated signal–row product marginal makes the row conditional kernel almost everywhere equal to the constant Gaussian law, by uniqueness of disintegration. With the other conditional marginal unchanged, this identifies the two reference measures after coordinate reordering; no general conditional chain rule is required.

## Expansion

Prove the conditional KL identity under the independent signal-row marginal, with extended-value conventions, then transport finiteness, entropy domination, and each density clause. Do not silently identify these divergences for an arbitrary correlated signal-row marginal.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L468-L488)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L181-L210)
