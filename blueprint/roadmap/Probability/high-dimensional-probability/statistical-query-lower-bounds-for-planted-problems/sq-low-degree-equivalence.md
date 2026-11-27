# Statistical query algorithms and low-degree tests are almost equivalent

Consider testing a null distribution $D_\emptyset$ on $\mathbb{R}^N$ against a family $S = \{D_u\}$ with a prior on $u$, where the $m$-sample problem draws $m$ i.i.d. samples. The problem is *$(\delta, k)$-nice* if no function of $k$ samples that is orthogonal to every function of degree at most $k$ in one of the samples distinguishes with advantage $\delta$; adding a small amount of coordinate-resampling noise makes a problem nice when it has no $k$-sample distinguisher. For an even $k > 0$ and an $(m^{-k/2}/4, k)$-nice problem:

1. if $\mathrm{SDA}(S, m') \le (2m/m')^{k/2}$ for some $m' \le m$, in particular if some statistical query algorithm makes $o(2^{k/2})$ queries to VSTAT$(m/3)$, then there is a good $4mk$-sample distinguisher of degree at most $k^2$;
2. if a degree-$k$ function is a good $m$-sample distinguisher, then $\mathrm{SDA}(S, m') \le (2m/m')^{O(k)}$ for some $m' \le m$, for example $\mathrm{SDA}(S, m) \le 2^{O(k)}$.

So, up to polynomial changes in the number of samples and in the degree, bounded low-degree advantage and large statistical dimension imply each other. For Gaussian additive-mean families and for product measures on $\{\pm 1\}^N$ the same conclusions hold without niceness, with degree $O(k)$ in part 1, provided there is no $k$-sample $2^k$-distinguisher. As corollaries, there are new statistical query lower bounds for sparse PCA, tensor PCA and several variants of planted clique, matching the low-degree predictions.

## Proof sketch

Both directions go through the moments of the pairwise correlations $\langle D_u, D_v \rangle - 1 = \chi_{D_\emptyset}(D_u, D_v)$ for independent $u, v$ from the prior. Expanding the $m$-sample likelihood ratio in samplewise degree, its low-degree norm is a polynomial in these correlations, with the $t$-th moment weighted by the number of ways to choose $t$ of the $m$ samples. A bound on the low-degree norm, together with niceness to control the purely high-degree part on $k$ samples, therefore bounds the moments, and a moment bound forces every not-too-small subfamily to have small average correlation, which is large statistical dimension. Conversely, large statistical dimension at every sample size $m' \le m$ bounds the moments $\mathbb{E}(\langle D_u, D_v\rangle - 1)^t$ for $t \le k/8$, and summing these bounds the low-degree norm.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](../low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)
- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Proof depends on

- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)
- [Low-degree advantage of the additive Gaussian model](../low-degree-likelihood-ratio-method/additive-gaussian-low-degree-advantage.md)

## Sources

- M. Brennan, G. Bresler, S. B. Hopkins, J. Li, T. Schramm, "Statistical Query Algorithms and Low-Degree Tests Are Almost Equivalent", COLT (2021), arXiv:2009.06107.
