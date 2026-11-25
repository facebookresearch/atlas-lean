# Weighted split conformal coverage under covariate shift

Let $\mathcal{X}$ be a measurable space, $P_X$ and $\tilde P_X$ probability measures on $\mathcal{X}$ with $\tilde P_X \ll P_X$, $\kappa$ a Markov kernel from $\mathcal{X}$ to $\mathbb{R}$ giving the conditional law of the response, and $w = d\tilde P_X / dP_X$ the Radon–Nikodym derivative (taken as a real number). Let $n \in \mathbb{N}$ and let the data $((X_1, Y_1), \dots, (X_n, Y_n); (X_{n+1}, Y_{n+1}))$ have law $(P_X \otimes \kappa)^{\otimes n} \otimes (\tilde P_X \otimes \kappa)$, and let $s : \mathcal{X} \times \mathbb{R} \to \mathbb{R}$ be a measurable score function. For $0 < \alpha < 1$,

$$\Pr\Big\{s(X_{n+1}, Y_{n+1}) \le Q_{1-\alpha}\big((s(X_i, Y_i))_{i \le n}, (p_i)_{i \le n}\big)\Big\} \ge 1 - \alpha, \qquad p_i = \frac{w(X_i)}{\sum_{j=1}^n w(X_j) + w(X_{n+1})},$$

where $Q_{1-\alpha}$ is the [weighted quantile](weighted-quantile.md), that is, the level-$(1 - \alpha)$ quantile of $\sum_i p_i \delta_{s(X_i, Y_i)} + p_{n+1} \delta_{+\infty}$.

In the source the coverage follows from weighted exchangeability of the data (independent draws whose laws are absolutely continuous with respect to each other are weighted exchangeable, Lemma 2) and a weighted quantile lemma (Lemma 3), which together give Theorem 2 and its covariate-shift case, Corollary 1.

## Background

- [Split conformal coverage](../split-conformal-prediction/of-real-one-sub-le-measure-coe-le-split.md): the unweighted guarantee recovered when $\tilde P_X = P_X$, so that $w \equiv 1$.
- [Criterion for lying below the weighted quantile](coe-le-weighted-quantile-iff.md): the coverage event as a condition on the weight of the scores strictly below the test score.

## Sources

- R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019, Corollary 1, for a score function that does not depend on the data bag, $S((x, y), Z) = s(x, y)$; this is the weighted split conformal case of their Section 2.2, which uses $s(x, y) = |y - \mu_0(x)|$ for a regression function $\mu_0$ fitted on independent data (the statement is conditional on that fit). The event is $Y_{n+1} \in \hat C_n(X_{n+1})$ for the band $\hat C_n(x) = \{y : s(x, y) \le \mathrm{Quantile}(1 - \alpha; \sum_i p_i(x) \delta_{V_i} + p_{n+1}(x) \delta_\infty)\}$.
