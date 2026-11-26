# Finite positive-contraction determinantal laws are strongly Rayleigh

Let $F$ be finite and nonempty, and let $K$ be a Hermitian complex matrix on $F$ satisfying $0\le c^*Kc\le c^*c$ for all complex column vectors $c$. There exists a probability law on subsets $X\subseteq F$ such that for every $A\subseteq F$,

$$
P(A\subseteq X)=\det K|_{A\times A}.
$$

Every law with those inclusion probabilities is strongly Rayleigh: its polynomial $\mathbb E\prod_{i\in X}z_i$ is zero-free on the product of open upper half-planes. The determinant on $A=\varnothing$ is $1$; no positive-definiteness or invertibility is assumed.

**Conventions.** Use Hermitian positive contractions, complex principal minors, and the [finite stability condition](binary-law-generating-models.md).

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Proof outline

The finite determinantal-law existence construction (including eigenvalues $0$ and $1$) and the determinant identity and nonvanishing argument for its generating polynomial.

Separate construction from stability. Verify the principal-minor inclusion identity for the constructed probability law and express the polynomial of any compatible law as the determinant of the same matrix pencil. Treat singular boundary cases by a direct compression or a justified limit, not by using $K^{-1}$ unconditionally.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L153-L160)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
