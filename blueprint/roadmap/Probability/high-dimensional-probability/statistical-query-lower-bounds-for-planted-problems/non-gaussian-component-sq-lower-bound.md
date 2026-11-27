# Statistical query lower bounds for non-Gaussian component analysis and robust estimation

Let $A$ be a distribution on $\mathbb{R}$ whose first $m$ moments agree with those of $\mathcal{N}(0,1)$ and with $\chi^2(A, \mathcal{N}(0,1)) < \infty$, and for a unit vector $v \in \mathbb{R}^n$ let $P_v$ be the distribution on $\mathbb{R}^n$ that is $A$ in direction $v$ and standard Gaussian in the orthogonal complement. Fix $0 < c < 1/2$ and $\varepsilon > 0$, let $n \ge m^{\Omega(1/c)}$, and suppose $d_{\mathrm{TV}}(P_v, P_{v'}) > 2\varepsilon$ whenever $|\langle v, v'\rangle| \le 1/8$. Every statistical query algorithm that, given access to $P_v$ for an unknown unit vector $v$, outputs a hypothesis $Q$ with $d_{\mathrm{TV}}(Q, P_v) \le \varepsilon$ needs at least $2^{\Omega(n^{c/2})} \ge n^{m+1}$ queries to STAT$\big(O(n)^{-(m+1)(1/4 - c/2)}\sqrt{\chi^2(A, \mathcal{N}(0,1))}\big)$ or to VSTAT$\big(O(n)^{(m+1)(1/2 - c)}/\chi^2(A, \mathcal{N}(0,1))\big)$. As consequences: learning mixtures of $k$ Gaussians requires $n^{\Omega(k)}$ statistical query complexity; robustly learning the mean of $\mathcal{N}(\mu, I_n)$ under an $\varepsilon$-fraction of corruptions to error $o(\varepsilon\sqrt{\log(1/\varepsilon)})$ requires super-polynomial statistical query complexity, so known efficient robust estimators are optimal among statistical query algorithms; robust covariance estimation in spectral norm and robust sparse mean estimation exhibit quadratic statistical-computational trade-offs; and robustly testing the mean of an identity-covariance Gaussian needs, information-theoretically, a number of samples linear in $n$.

## Proof sketch

A random packing gives $2^{\Omega(n^c)}$ unit vectors with pairwise inner products $O(n^{c - 1/2})$; by the lemma the corresponding planted distributions have pairwise correlations at most $O(n)^{-(m+1)(1/2 - c)}\chi^2$, so the statistical dimension of this search problem at that correlation is large, and the statistical-dimension lower bound for search problems gives the stated query bound with tolerance the square root of the correlation. Each application constructs a one-dimensional distribution $A$ matching many Gaussian moments that is a mixture of Gaussians or an $\varepsilon$-corruption of a shifted Gaussian.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)
- [Relations between STAT and VSTAT oracles and their simulation from samples](stat-vstat-relations-and-simulation.md)

## Proof depends on

- [Hidden-direction distributions matching m moments have tiny pairwise correlations](hidden-direction-correlation-bound.md)
- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)

## Sources

- I. Diakonikolas, D. M. Kane, A. Stewart, "Statistical Query Lower Bounds for Robust Estimation of High-Dimensional Gaussians and Gaussian Mixtures", FOCS (2017), arXiv:1611.03473.
