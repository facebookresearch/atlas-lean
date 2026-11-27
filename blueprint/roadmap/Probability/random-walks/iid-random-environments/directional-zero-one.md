# A directional zero–one law under strict ellipticity

Let $d\ge3$ and $\nu$ be a probability law on rows of $2d$ nonnegative transition probabilities for the steps $\pm e_i$ (a row sums to one). Assume $\nu$-almost surely each entry is strictly positive. Independently sample a row from $\nu$ at every vertex of $\mathbb Z^d$, keep this environment fixed, and run the walk from zero using the row at its current vertex. Write $P_\nu$ for the path law averaged over the sampled environment. For every $\ell\in\mathbb R^d\setminus\{0\}$,

$$
P_\nu(\langle X_n,\ell\rangle\to+\infty)\in\{0,1\}.
$$

No uniform lower bound on the transition probabilities is assumed.

**Conventions.** Use the product environment, the Markov path law on pairs of fixed environment and current site, and the pushforward to site paths. This is not an IID-increment walk or one that resamples a row on each visit.

## Depends on

- [IID nearest-neighbor environments and the annealed path law](nearest-neighbor-environment-law.md)

## Expansion

State the fresh-environment path comparison with its boundary conditioning and strict ellipticity assumptions, and isolate exclusion of simultaneous positive probabilities of opposite directional escape in the required dimension. Show how the comparison forces the stated zero-or-one law for every nonzero direction without invoking an independent tail law for the path increments.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectionalWalk.lean#L85-L89)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/220.md)
- [Accompanying manuscript: A directional zero–one law under strict ellipticity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-directional-zero-one-law-under-strict-ellipticity-September-23-2026/paper.pdf)
