# Fourier bounds from complementary partial-permutation coset caps

Partition a finite set $X$ into $b>0$ nonempty disjoint blocks $M_i$. Let $G=\operatorname{Sym}(X)$ and $H_i$ be the permutations fixing every point outside $M_i$. Take nonnegative $f:G\to\mathbb R$ of total mass at most one. Suppose for every $i$ and $g\in G$ the mass $\sum_{h\in H_i}f(gh)$ is at most $B/[G:H_i]$. For a unitary irreducible complex representation $\rho$ of dimension $D$, set $\widehat f=\sum_g f(g)\rho(g)$. For every $u>0$ let $C(u)=\sup_{n\ge1}\sum_{\lambda\in\widehat{S_n}}(\dim\lambda)^{-u}$, taking one dimension from each irreducible isotypic component of the left regular representation. Then both $\operatorname{tr}(\widehat f^*\widehat f)$ and $\|\widehat f\|_{\rm op}^2$ are bounded by $bBC(u)D^{-1+(u+2)/b}$.

**Conventions.** Use the left cosets of block-fixing subgroups, the finite symmetric-group irreducible degrees, and unnormalized Fourier and Hilbert–Schmidt norms. In particular the cap is divided by the subgroup index, not an absolute mass cap of $B$.

The degree constant uses a totalized real supremum. Finiteness at each positive parameter is a proof ingredient, not a claim of this definition.

## Depends on

The statement uses the explicit definitions given above.

## Proof depends on

Symmetric-group inverse-degree bounds and a coset-wise Plancherel or restriction estimate converting all caps into one high-dimensional representation bound.

## Expansion

Identify the irreducible index with a canonical Specht classification without replacing isotypic dimensions by multiplicity-weighted dimensions. Prove the Hilbert–Schmidt estimate before using operator norm domination. The statement asserts no asymptotic consequence for a product of two random permutations.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartialPermutation.lean#L110-L112)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: From partial permutation information to Fourier bounds](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/main.pdf)
- [Pinned definitions used inline](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PartialPermutation.lean#L10-L98)
