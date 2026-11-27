# Inverse Gram-volume moments from all-scale ball control

There are $C>0$ and $d_0$ such that for every $d\ge d_0$, every probability $\nu$ on Euclidean $\mathbb R^d$ with $\nu(B(x,r))\le r^{(d-1)/2}$ at every center $x$ and every radius $r>0$ (open balls), and every deterministic $u\in\mathbb R^d$, the following holds. For $k=\lfloor d/100\rfloor$ independent samples $Z_i$ of law $\nu$, put $V=[\det(\langle Z_i-u,Z_j-u\rangle)_{i,j\le k}]^{1/2}$. Then $\mathbb E[V^{-k}]\le e^{Cdk}$ as an extended nonnegative integral. In particular reciprocal powers use the extended inverse at zero, not a default zero. No support or density assumption is made.

**Conventions.** Use Euclidean Gram determinants, independent product sampling, small-ball probabilities at every scale and extended reciprocal integration.

## Depends on

The statement uses the explicit definitions given above.

## Expansion

Successive distances to the random affine spans in the Gram–Schmidt factorization, controlled by subspace-neighborhood estimates derived from the all-center ball bound even without bounded support.

Prove a conditional inverse-distance moment in the relevant codimension with sufficient decay at small radius. Factor the Gram volume without dividing at a zero determinant, and integrate successively under the independent sample law.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L138-L139)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf)
- [Pinned definitions used inline](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L112-L137)
