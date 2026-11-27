# An invariant determinantal law is an equivariant IID factor

Let $\Gamma$ be a countable group. Suppose $K$ is Hermitian with every finite principal compression a positive contraction, and $\mu$ is a binary law with all finite inclusion probabilities equal to the corresponding principal minors of $K$. If $\mu$ is invariant under all left shifts, there is a measurable map from the IID uniform $[0,1]$ label space to the binary configuration space that commutes pointwise with every left shift and has pushforward law $\mu$. The premise is invariance of the law; invariance of the entries of $K$ is not required.

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Proof depends on

- [Invariant strongly Rayleigh laws are equivariant factors of IID](invariant-rayleigh-iid-factor.md)
- [Finite positive-contraction determinantal laws are strongly Rayleigh](finite-positive-contraction-law.md)

## Proof outline

Finite determinantal stability on all marginals and the equivariant sampling theorem for invariant strongly Rayleigh laws.

Push the inclusion identity to each finite restriction, use the finite stability theorem, and route the resulting countable strongly Rayleigh law through the factor construction. Keep the same $\mu$ throughout.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L167-L173)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
