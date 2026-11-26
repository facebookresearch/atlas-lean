# Reciprocal Specht degrees and the eight-block Fourier bound

Let $D_\lambda$ be the degree of the complex Specht space of partition $\lambda$ of $n$, using the span of translates of the column-alternating base row tabloid. The sequence $A_n=\sum_{\lambda\vdash n}D_\lambda^{-1}$, $n\ge1$, is bounded with $A_n\le C_1=\sup_{m\ge1}A_m$, and its restricted sum over diagrams whose longest row and longest column are both shorter than $n$ tends to zero.

For $d\ge3$, fix any identification of the $2^d$ cube positions with $[8]\times[2^{d-3}]$. Write $G$ for the whole symmetric group and $H_i$ for the subgroup permuting the fiber at the $i$th first coordinate and fixing all other fibers. For any probability masses $\nu$ with $\sum_{h\in H_i}\nu(gh)\le4|H_i|/|G|$ for every $i,g$, and any unitary irreducible complex representation $\rho$ of dimension $D$,

$$
\left\|\sum_g\nu(g)\rho(g)\right\|_{\rm op}\le\sqrt{32C_1}\,D^{-5/16}.
$$

**Conventions.** Use the tabloid Specht degree model, the one-row and one-column exclusions, and the eight prescribed left-coset caps for the block partition.

## Depends on

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)

## Proof depends on

- [Fourier bounds from complementary partial-permutation coset caps](fourier-bound-from-coset-caps.md)

A reciprocal-degree estimate uniform in $n$, with the nontrivial-degree contribution vanishing, and the block Fourier estimate at those constants and exponent.

## Expansion

Separate bounded reciprocal sums from their restricted asymptotic. For the Fourier estimate verify that the dimensions indexing the constant agree with the irreducible index in the [complementary-coset estimate](fourier-bound-from-coset-caps.md), then specialize at $b=8$, $B=4$, $u=1$ and take the square root.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThorpFirstReciprocal.lean#L205-L226)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Optimal-order mixing of the Thorp shuffle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Optimal-order-mixing-of-the-Thorp-shuffle-September-26-2026/paper.pdf)
