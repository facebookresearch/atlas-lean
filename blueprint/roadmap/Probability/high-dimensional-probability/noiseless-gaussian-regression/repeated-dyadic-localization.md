# Repeated dyadic localization for exact Gaussian observations

For large $n$, let $Z$ be uniform on the half-open cube $[-1/(2\sqrt n),1/(2\sqrt n))^n$ and $s(Z)=(Z,\sqrt{1-\|Z\|_2^2})$. In each of $t$ blocks draw $\lfloor n/16\rfloor$ fresh independent standard Gaussian rows in $\mathbb R^{n+1}$ along with their exact inner-product labels with $s(Z)$. At block $i$, for every past output history in $[N]^i$, allow an arbitrary measurable probability kernel from the block and its labels to $[N]$. The likelihood of a full history given $Z=z$ is the product of the corresponding conditional block probabilities integrating fresh Gaussian rows.

A disclosure at each step is a measurable finite-range function of $Z$ and the output history through that block. It gives a half-open aligned dyadic subcell of the initial cube, at a natural level $J$ with side length $1/(\sqrt n\,2^J)$ and indices in $[2^J]^n$. For every signal point in the cube and every history, the cell contains the point and the cells are nested in time. The final level is the level of the last disclosed cell if $t>0$, and is zero if $t=0$.

There exist absolute $c>0$ and $n_0$ such that, for every $C_0>0$, some $C>0$ works for all $n\ge n_0$, $N\ge1$, $t$, and rules above under

$$
(2/\lfloor n/8\rfloor+e^{-c\lfloor n/16\rfloor})\log N\le C_0(n+1).
$$

Then there are disclosures for which the mutual information of $Z$ with the pair (full output history, full disclosure history) is at most $C(n+1)t$ and the expected final level is at most $Ct$. Mutual information is KL divergence of the joint law from the product of marginals, in nats and extended nonnegative reals.

**Conventions.** Use the cube-to-sphere chart, exact Gaussian block likelihoods, finite-history law, half-open dyadic cells, and nested finite-range disclosure.

## Depends on

- [Dyadic cell disclosures and Gaussian block localization](models/dyadic-cell-localization-model.md)


## Proof depends on

An entropy-aware one-block localization comparison and a regularization scheme controlling the accumulated expected depth; exact row information cannot simply be replaced by a fresh independent surrogate.

## Expansion

Show posterior measurability at all histories and prove the one-block increment bound under the stated memory-size inequality. Track finite-range disclosure and nesting at every depth and derive the chain rule for the augmented history. Check the exact $n/8$ and $n/16$ rounded dimensions and the empty-history case.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L104-L106)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf)
- [Pinned experiment definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L11-L94)
