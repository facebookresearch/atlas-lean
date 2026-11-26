# A unique determinantal law for a countable positive-contraction kernel

For a countable set $I$ (which may be empty), let $K:I\times I\to\mathbb C$ be Hermitian. Assume that every finite principal restriction satisfies $0\le c^*Kc\le c^*c$ for all complex vectors on that finite set. Then exactly one probability law on $\{0,1\}^I$ satisfies $P(X_i=1\text{ for every }i\in A)=\det K|_{A\times A}$ for each finite $A$, with empty determinant $1$. There is no global trace-class condition.

**Conventions.** Use countable product configuration spaces, the finite-compression definition of a Hermitian positive contraction, and cylinder inclusion probabilities.

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Proof depends on

- [Existence for finite positive contractions](finite-positive-contraction-law.md)

## Proof outline

Use finite inclusion–exclusion for ordinary cylinders and measure extension for consistent finite laws.

Show the law on every finite subset is uniquely determined by the inclusion probabilities by Möbius inversion. The resulting finite laws are consistent under restriction, so extend them to the product and use cylinders for uniqueness; handle the empty set as a point law.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L161-L166)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
