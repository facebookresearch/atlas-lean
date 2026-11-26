# Glivenko–Cantelli theorem

The empirical distribution function $F_N(x) = \#\{1 \le i \le N : X_i \le x\}/N$ of an i.i.d. sample $X_1, \dots, X_N$
estimates the distribution function $F$ with no assumption on $F$. The Glivenko–Cantelli theorem
says that $\sup_x \lvert F_N(x) - F(x) \rvert \to 0$ almost surely. The Dvoretzky–Kiefer–Wolfowitz
inequality makes this quantitative and non-asymptotic:
$P(\sup_x \lvert F_N(x) - F(x) \rvert > \varepsilon) \le 2 e^{-2N\varepsilon^2}$ for every $N$, every
$\varepsilon > 0$ and every $F$, with Massart's constant $2$. Inverting it gives the
distribution-free confidence band $F_N \pm \sqrt{\log(2/\alpha)/(2N)}$ for the whole function $F$.

- [Empirical count](empirical-count.md)
- [Glivenko–Cantelli theorem](glivenko-cantelli.md)
- [Empirical distribution function of a finite sample](emp-cdf.md)
- [Pointwise Hoeffding bound for the empirical distribution function](abs-emp-cdf-sub-le.md)
- [Empirical distribution functions are right-continuous](emp-cdf-right-continuous.md)
- [Suprema of right-continuous deviations can be taken over the rationals](i-sup-abs-sub-eq-i-sup-rat.md)
- [The uniform deviation of an empirical distribution function is a supremum over the rationals](uniform-deviation-eq-i-sup-rat.md)
- [Measurability of the uniform deviation event](measurable-set-uniform-deviation.md)
- [Distribution-free reduction of the Kolmogorov–Smirnov distance by quantile coupling](ks-reduction-quantile-coupling-emp-cdf.md)
- [Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant](measure-exists-abs-empirical-cdf-sub-gt.md)

## Related topics

- [Kaplan–Meier estimator](../kaplan-meier-estimator/README.md): without censoring the Kaplan–Meier estimate is the empirical survival function $1 - F_N$, so these results describe its uncensored case.
- [Bootstrap and the Mallows metric](../../statistical-estimation/bootstrap-and-the-mallows-metric/README.md): the bootstrap resamples from the empirical law; its consistency rests on the convergence of the empirical law, there in the Mallows metric.
- [Two-groups model and local false discovery rates](../../hypothesis-testing/two-groups-model-and-local-false-discovery-rates/README.md): Efron's empirical-Bayes estimate of the tail-area false discovery rate replaces the mixture distribution function of the z-values by their empirical distribution function, whose uniform accuracy these results control.
- [Split conformal prediction](../../hypothesis-testing/split-conformal-prediction/README.md): the DKW inequality controls the empirical quantiles of calibration residuals; Lei, G'Sell, Rinaldo, Tibshirani and Wasserman use it in their analysis of the length of split conformal intervals (arXiv:1604.04173v2, proof of Theorem 2.4).
