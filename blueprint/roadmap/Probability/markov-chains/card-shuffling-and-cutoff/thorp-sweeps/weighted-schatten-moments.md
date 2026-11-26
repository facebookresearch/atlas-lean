# Uniform weighted Schatten moments of a coordinate sweep

For $d\ge1$ define an elementary shuffle of a Boolean $d$-cube of positions by fair independent swaps in pairs differing in the first bit, then cyclic reindexing of bits $x'_i=x_{i+1\bmod d}$. A sweep applies $d$ independent elementary shuffles. For a Young diagram $\mu$ of size $2^d$, let $D_\mu=\dim V_\mu$ for its tabloid Hilbert Specht representation relabelled to the cube, and $Q_{d,\mu}=\mathbb E\rho_\mu(\pi)$ for the sweep permutation. Write $\|Q\|_{S_p}^p=\sum_i s_i(Q)^p$ with singular values counted without division by dimension.

There exist a positive weight $W(\mu)$ on all Young diagrams, $p_*\ge2$, and a real sequence $(p_d)_{d\in\mathbb N}$ independent of the shape $\mu$, with $2\le p_d\le p_*$ for every $d\ge1$, such that for every such diagram

$$
D_\mu^{3/4}\le W(\mu)\le D_\mu,\quad W(\mu)\|Q_{d,\mu}\|_{S_{p_d}}^{p_d}\le1,\quad
\|Q_{d,\mu}\|_{\rm op}\le D_\mu^{-3/(4p_*)}.
$$

**Conventions.** Use the physical pair-step and $d$-step law, the tabloid Specht module with cube relabelling, and unnormalized singular-value moments with real exponent.

## Depends on

- [Physical Thorp pair steps and Specht Fourier averages](physical-thorp-step-and-specht-averages.md)

- [Tabloid Specht modules and all-copy subgroups on occupied boards](occupied-board-specht-model.md)

## Expansion

Uniform Fourier contraction across all Specht types, including the row–column overlap and weighted-moment estimates that supply one bounded exponent schedule rather than exponents chosen separately for each representation.

Prove the link between shuffle steps and chronological coordinate layers. Build the common Specht and singular-value API, bound the weighted moments uniformly, then derive the operator estimate by taking a $p_d$-th root and using $p_d\le p_*$. The weights are a single function on diagrams.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeightedSweepMoments.lean#L287-L299)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Row–column symmetry and contraction of coordinate sweeps](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf)
