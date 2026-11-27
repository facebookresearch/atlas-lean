# An equivariant determinantal process from an invariant kernel

Let $\Gamma$ be a countable group and $K:\Gamma^2\to\mathbb C$ Hermitian with every finite principal compression a positive contraction. Suppose $K(gh,gk)=K(h,k)$ for all $g,h,k$. There exists a probability law $\mu$ on binary configurations with $P(X_i=1\text{ for every }i\in A)=\det K|_{A\times A}$ for all finite $A$, invariant under left shifts and the pushforward of IID uniform $[0,1]$ labels by a measurable pointwise left-equivariant map.

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Proof depends on

- [Countable existence and uniqueness](countable-positive-contraction-law.md)
- [An IID factor for the invariant law](invariant-determinantal-iid-factor.md)

## Proof outline

Translate finite coordinate sets and observe that the corresponding principal determinants are unchanged. Use law uniqueness to prove invariance before using the invariant-factor result. Kernel invariance is a premise here, unlike the theorem with an already specified invariant law.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L174-L180)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
