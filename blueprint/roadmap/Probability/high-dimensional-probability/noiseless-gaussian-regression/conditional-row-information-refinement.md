# Conditional row information under deterministic message refinement

Let $P$ be any probability law of $(S,W,X)$ on the unit sphere in $\mathbb R^d$, a countable singleton-measurable message space, and $m$ Euclidean rows. Suppose $(S,X)$ has law $\nu\otimes\gamma_m$ for a probability $\nu$ and product standard Gaussian row law $\gamma_m$. Append $e(S,W)$ to the message for any measurable deterministic function into another countable singleton-measurable space. If the countable entropy in nats of $(W,e(S,W))$ is finite, then

$$
I(X;(W,e(S,W))\mid S)=I(X;W\mid S),
$$

as extended nonnegative KL divergences against the corresponding conditionally independent laws. No absolute continuity of $\nu$ relative to surface measure is required.

The conditional information is the extended KL divergence of the law in coordinate order $(S,X,W)$ from its signal marginal composed with the product of the two marginal kernels of the disintegration of $(X,W)$ given $S$. For the refined side replace $W$ everywhere by the ordered pair $(W,e(S,W))$. The source definition returns zero if the row–message space is empty; probability of the given joint law rules out that case. It is not the finite-PMF conditional mutual information.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)

## Proof depends on

- [Row relative entropy under deterministic message refinement](../../linear-models-multivariate/gaussian-row-kl-message-refinement.md)

## Proof outline

Under the independent signal–row marginal, project the disintegration to the row coordinate. Composing that marginal kernel with the signal marginal gives $\nu\otimes\gamma_m$, so uniqueness gives the constant Gaussian kernel almost everywhere. Replacing it by that constant shows that the conditional reference is exactly the product reference of the linked result, up to coordinate reordering. The append map preserves the signal–row marginal, so the same identification applies on both sides.

Use the deterministic refinement kernel that is reversible by forgetting the new coordinate, preserving the conditional product references. Confirm the exact finite entropy premise and not just a uniform support bound on $W$. This is a statement about conditional information, not the unconditioned reference-divergence definition.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L489-L501)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
