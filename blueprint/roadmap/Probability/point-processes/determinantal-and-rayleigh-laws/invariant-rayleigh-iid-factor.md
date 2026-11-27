# Invariant strongly Rayleigh laws are equivariant factors of IID

Let $\Gamma$ be a countable group and $\mu$ a probability law on binary configurations on $\Gamma$, invariant under each left shift $(g\cdot x)_h=x_{g^{-1}h}$. Suppose every finite marginal is strongly Rayleigh: on any finite $F\subset\Gamma$, its generating polynomial is $\mathbb E_\mu\prod_{i\in F:X_i=1}z_i$ and is nonzero whenever all $z_i$ are in the open upper half-plane. Then there exists a measurable map from IID uniform $[0,1]$ vertex labels to binary configurations with pushforward law $\mu$, commuting with each shift for every input label configuration. Neither amenability nor finite generation is required.

**Conventions.** Use finite strongly Rayleigh marginals, product measures on countable configuration spaces, left shifts, and the pointwise equivariance condition.

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Expansion

A Borel equivariant sampling theorem for invariant laws with stochastic covering or the corresponding conditional consistency estimates. A realization of the law by arbitrary independent uniforms is not enough.

Prove the finite marginal conditional comparison and the consistency of the ordered conditional sampler under shifts. Account for exceptional label configurations in a shift-stable way to obtain equivariance everywhere, not merely almost everywhere for each shift.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L147-L152)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
