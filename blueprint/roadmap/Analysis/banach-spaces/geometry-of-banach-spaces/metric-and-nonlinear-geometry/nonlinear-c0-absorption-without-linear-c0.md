# Nonlinear absorption of c₀ without a linear copy

Let $c_0$ be the real Banach space of sequences on $\mathbb N$ tending to zero with the supremum norm. There is a separable real Banach space $Z$ with no bounded linear map $S:c_0\to Z$ having a lower norm bound $c\|x\|\le\|Sx\|$ for all $x$ and some $c>0$. There is a surjective bi-Lipschitz map $Z\times c_0\to Z$ for the maximum product metric, there is a bi-Lipschitz map $c_0\to Z$, and every separable metric space in the same universe admits a bi-Lipschitz map into $Z$. Here bi-Lipschitz means lower and upper distance bounds with constants $0<c\le C$. There is no bounded linear isomorphism $Z\times c_0\cong Z$ with bounded inverse.

## Depends on

- Real null sequences, maximum-product Banach spaces, and the two-sided metric and linear norm bounds above.

## Proof depends on

- Construction of one separable complete space with both metric universality and exclusion of linear copies of $c_0$, and a surjective absorption map on that same space.

## Expansion

Separate the normed-space construction and the exclusion argument from the metric embedding and onto absorption estimates. Use the isometric $c_0$ product factor to deduce the obstruction to a linear isomorphism. Keep all consequences on the same witness.

## Sources

- OpenAI, [C0Absorption comparator, main_result](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/C0Absorption.lean#L29-L30).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/324.md).
