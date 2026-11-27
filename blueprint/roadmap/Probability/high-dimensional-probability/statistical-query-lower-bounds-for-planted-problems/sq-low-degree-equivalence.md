# Statistical query algorithms and low-degree tests are almost equivalent

Consider testing a null distribution $D_\emptyset$ on $\mathbb{R}^N$ against a family $S = \{D_u\}$ with a prior $\mu$ on $u$, where the $m$-sample problem draws $m$ i.i.d. samples. With relative densities $\bar D_u = D_u/D_\emptyset$ and $\langle f, g\rangle = \mathbb{E}_{D_\emptyset}[fg]$, the statistical dimension used here (Brennan et al., Definition 1.2) is

$$
\mathrm{SDA}(S, m) = \max\Bigl\{q \in \mathbb{N} : \mathbb{E}_{u, v \sim \mu}\bigl[\langle \bar D_u, \bar D_v\rangle - 1 \bigm| A\bigr] \le \tfrac{1}{m} \text{ for every event } A \text{ with } \Pr_{u, v \sim \mu}(A) \ge \tfrac{1}{q^2}\Bigr\},
$$

where $u, v$ are independent and $A$ ranges over all events on pairs $(u, v)$, not only squares $\mathcal{H}' \times \mathcal{H}'$ of subfamilies. For $\beta > 0$, a function $p$ of $m$ samples is an *$m$-sample $\beta$-distinguisher* (Brennan et al., Definition 1.1) if

$$
\mathbb{E}_{x \sim D_\emptyset^{\otimes m}} p(x) - \mathbb{E}_{u \sim \mu}\,\mathbb{E}_{x \sim D_u^{\otimes m}} p(x) > \beta \sqrt{\mathrm{Var}_{x \sim D_\emptyset^{\otimes m}} p(x)},
$$

and it is *good* if it is a $\beta$-distinguisher for some $\beta > 1$. The problem is *$(\delta, k)$-nice* (Definition 1.4) if no function of $k$ samples that is orthogonal under $D_\emptyset^{\otimes k}$ to every function of degree at most $k$ in one of the samples is a $k$-sample $\delta$-distinguisher; when $D_\emptyset$ is a product distribution and the problem has no $k$-sample $C$-distinguisher, resampling each coordinate independently with a small probability makes it nice (Fact 1.5). For an even $k > 0$ and an $(m^{-k/2}/4, k)$-nice problem:

1. if $\mathrm{SDA}(S, m') \le (2m/m')^{k/2}$ for some $m' \le m$, in particular if some statistical query algorithm makes $o(2^{k/2})$ queries to VSTAT$(m/3)$, then there is a good $4mk$-sample distinguisher of degree at most $k^2$;
2. if a degree-$k$ function is a good $m$-sample distinguisher, then $\mathrm{SDA}(S, m') \le (2m/m')^{O(k)}$ for some $m' \le m$, for example $\mathrm{SDA}(S, m) \le 2^{O(k)}$.

So, up to polynomial changes in the number of samples and in the degree, bounded low-degree advantage and large statistical dimension imply each other. For Gaussian additive-mean families ($D_\emptyset = \mathcal{N}(0, I_N)$, $D_u = \mathcal{N}(u, I_N)$) and for families in which $D_\emptyset$ and every $D_u$ are product measures on $\{\pm 1\}^N$, the same conclusions hold without niceness, with degree $O(k)$ in part 1, provided $k \ll m$ and there is no $k$-sample $2^k$-distinguisher. As corollaries, there are new statistical query lower bounds for sparse PCA, tensor PCA and several variants of planted clique, matching the low-degree predictions.

## Proof sketch

Both directions go through the moments of the pairwise correlations $\langle D_u, D_v \rangle - 1 = \chi_{D_\emptyset}(D_u, D_v)$ for independent $u, v$ from the prior. Expanding the $m$-sample likelihood ratio in samplewise degree, its low-degree norm is a polynomial in these correlations, with the $t$-th moment weighted by the number of ways to choose $t$ of the $m$ samples. A bound on the low-degree norm, together with niceness to control the purely high-degree part on $k$ samples, therefore bounds the moments, and a moment bound forces the conditional mean of $\langle \bar D_u, \bar D_v\rangle - 1$ to be small on every event of not-too-small probability, which is large statistical dimension. Conversely, large statistical dimension at every sample size $m' \le m$ bounds the moments $\mathbb{E}(\langle D_u, D_v\rangle - 1)^t$ for $t \le k/8$, and summing these bounds the low-degree norm.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](../low-degree-likelihood-ratio-method/low-degree-likelihood-ratio.md)
- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Proof depends on

- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)
- [Low-degree advantage of the additive Gaussian model](../low-degree-likelihood-ratio-method/additive-gaussian-low-degree-advantage.md)

## Sources

- M. Brennan, G. Bresler, S. B. Hopkins, J. Li, T. Schramm, "Statistical Query Algorithms and Low-Degree Tests Are Almost Equivalent", COLT (2021), arXiv:2009.06107, Definitions 1.1, 1.2 and 1.4, Fact 1.5 and Theorems 1.6 and 1.7.
