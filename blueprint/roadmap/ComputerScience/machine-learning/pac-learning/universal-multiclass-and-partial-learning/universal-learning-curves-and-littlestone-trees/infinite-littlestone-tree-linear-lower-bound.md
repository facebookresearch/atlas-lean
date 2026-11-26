# An infinite Littlestone tree forbids rates faster than linear

If $H$ has an infinite Littlestone tree, then $H$ is not learnable faster than $1/n$: for every learner there are a realizable distribution $P$ and $C, c > 0$ such that $\mathbb{E}[\mathrm{er}_P(\hat h_n)] \ge \dfrac{C}{cn}$ for infinitely many $n$.

## Proof sketch

Choose a random branch $y \in \{0,1\}^{\mathbb{N}}$ of the infinite tree uniformly and let $P_y$ put mass proportional to $2^{-k}$ on the point at depth $k$ along the branch, labelled by the branch; every $P_y$ is realizable because every finite branch is realized. For a sample of size $n$, the first depth whose point is not observed has mass of order $1/n$ with constant probability, and the label there is an unbiased coin independent of the sample. Averaging over branches, the expected error is $\Omega(1/n)$ along a subsequence, and a fixed branch achieving it exists by Fatou's lemma.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
