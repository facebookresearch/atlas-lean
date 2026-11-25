# Exact split conformal coverage without ties

Let $n \in \mathbb{N}$ and let $\mu$, the law of the score vector, be a probability measure on $\mathbb{R}^{n+1}$ invariant under every coordinate permutation, under which the $n + 1$ scores are almost surely distinct. Then for every $1 \le k \le n + 1$ the test score is covered by the $k$-th smallest calibration score ($+\infty$ if $k = n + 1$) with probability exactly $k/(n + 1)$:

$$\mu\big(\omega_{n+1} \le \hat q_k(\omega)\big) = \frac{k}{n + 1}.$$

The proof follows the source: the test score is covered iff fewer than $k$ of all $n + 1$ scores lie strictly below it, i.e. iff it is among the $k$ smallest; when the scores are distinct exactly $k$ of the $n + 1$ positions have that property, and averaging over the permutation group turns this count into the probability $k/(n + 1)$.

## Informally uses

- [Exactly $k$ coordinates have rank count below $k$](card-filter-rank-count-lt-of-injective.md): the deterministic count of positions among the $k$ smallest when there are no ties.
- [Coverage through the strict lower count](coe-le-split-conformal-threshold-iff.md): coverage is the rank condition "fewer than $k$ scores strictly below".
- [Averaging over an invariant finite group](../permutation-tests/measure-eq-card-div-of-ae-card-filter-sm.md): the exchangeability step, turning an almost-sure count of permutations into a probability.

## Background

- [Split conformal coverage](of-real-one-sub-le-measure-coe-le-split.md): the lower bound $1 - \alpha$, which holds with ties.

## Sources

- R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019, proof of Lemma 1 ("when there are almost surely no ties, it holds with probability exactly $\lceil\beta(n+1)\rceil/(n+1)$").
