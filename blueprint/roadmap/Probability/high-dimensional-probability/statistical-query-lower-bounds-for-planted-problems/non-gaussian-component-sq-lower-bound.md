# Statistical query lower bounds for non-Gaussian component analysis and robust estimation

In the setting of the moment-matching lemma, every statistical query algorithm that distinguishes $\mathcal{N}(0, I_n)$ from $P_v$ for an unknown direction $v$ (or finds $v$) requires, for every $c < 1/2$, either $2^{\Omega(n^c)}$ queries or at least one query of tolerance at most $n^{-(m+1)(1/4 - c/2)}\sqrt{\chi^2(A, \mathcal{N}(0,1))}$. As consequences: learning mixtures of $k$ Gaussians requires $n^{\Omega(k)}$ statistical query complexity; robustly learning the mean of $\mathcal{N}(\mu, I_n)$ under an $\varepsilon$-fraction of corruptions to error $o(\varepsilon\sqrt{\log(1/\varepsilon)})$ requires super-polynomial statistical query complexity, so known efficient robust estimators are optimal among statistical query algorithms; robust covariance estimation in spectral norm and robust sparse mean estimation exhibit quadratic statistical-computational trade-offs; and robust mean testing needs a number of samples linear in $n$.

## Proof sketch

Packing arguments give $2^{\Omega(n^c)}$ unit vectors with pairwise inner products at most $n^{c - 1/2}$; by the lemma the corresponding planted distributions have pairwise correlations at most $n^{-(m+1)(1/2 - c)}\chi^2$, so the statistical dimension with this average correlation is $2^{\Omega(n^c)}$, and the statistical-dimension theorem gives the bound with tolerance the square root of the correlation. Each application constructs a one-dimensional distribution $A$ matching many Gaussian moments that is a mixture of Gaussians or an $\varepsilon$-corruption of a shifted Gaussian.

## Depends on

- [Hidden-direction distributions matching m moments have tiny pairwise correlations](hidden-direction-correlation-bound.md)
- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)

## Proof depends on

- [Hidden-direction distributions matching m moments have tiny pairwise correlations](hidden-direction-correlation-bound.md)
- [Statistical dimension lower bounds statistical query complexity](statistical-dimension-query-lower-bound.md)

## Sources

- I. Diakonikolas, D. M. Kane, A. Stewart, "Statistical Query Lower Bounds for Robust Estimation of High-Dimensional Gaussians and Gaussian Mixtures", FOCS (2017), arXiv:1611.03473.
