# Upper bound on split conformal coverage without ties

Let $n \in \mathbb{N}$ and let $\mu$, the law of the score vector, be a probability measure on $\mathbb{R}^{n+1}$ invariant under every coordinate permutation, under which the scores are almost surely distinct. For $0 \le \alpha < 1$ and $k = \lceil (1 - \alpha)(n + 1) \rceil$,

$$\mu\big(\omega_{n+1} \le \hat q_k(\omega)\big) \le 1 - \alpha + \frac{1}{n + 1}.$$

Together with the lower bound this pins the coverage between $1 - \alpha$ and $1 - \alpha + 1/(n + 1)$: split conformal prediction is not only valid but nearly exact. Without the no-ties assumption the upper bound fails (for example, if all scores are equal the coverage is $1$).

## Informally uses

- [Exact split conformal coverage without ties](measure-coe-le-split-conformal-threshold.md): the coverage is exactly $\lceil (1 - \alpha)(n + 1) \rceil / (n + 1) < 1 - \alpha + 1/(n + 1)$.

## Background

- [Split conformal coverage](of-real-one-sub-le-measure-coe-le-split.md): the matching lower bound.

## Sources

- R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019, Lemma 1 (with $\beta = 1 - \alpha$), which states this bound for $\beta \in (0, 1)$; the statement above also admits the trivial endpoint $\alpha = 0$. Lemma 2 of Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222, is stated with the term $1/n$; the bound above is the sharper $1/(n + 1)$.
- J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani and L. Wasserman, *Distribution-free predictive inference for regression*, arXiv:1604.04173v2 (9 March 2017); J. Amer. Statist. Assoc. 113 (2018) 1094–1111. Theorem 2.2 of the arXiv version (the one read), second part: the bound $1 - \alpha + 2/(n + 2)$ for $n$ points split into equal halves, which is $1 - \alpha + 1/(n_2 + 1)$ with $n_2 = n/2$ calibration points, assuming that the residuals have a continuous joint distribution.
