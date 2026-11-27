# Proper learners attain the optimal PAC rate exactly when the dual Helly number is bounded

If the dual Helly number of $H$ is finite, there exists a proper learner for $H$ (one that always outputs a concept of $H$) with sample complexity $O\big((d + \log(1/\delta))/\varepsilon\big)$ for VC dimension $d$, the constant depending on the dual Helly number. Conversely, if $H$ is closed, that is, every set of labelled examples consistent with no concept of $H$ has a finite subset consistent with no concept of $H$, and its dual Helly number is infinite, then every proper learner for $H$ needs an extra $\log(1/\varepsilon)$ factor in the joint dependence on $\varepsilon$ and $\delta$. So for closed classes a proper learner attains the optimal rate if and only if the dual Helly number is finite.

## Proof sketch

When the dual Helly number is $k$, a proper learner can output a concept consistent with a majority-like aggregate: the realizable region of the aggregate of $O(\log(1/\delta))$ ERM outputs is consistent on every $k$-subsample with high probability, hence globally consistent by the Helly property, and the improper majority vote analysis transfers to this proper hypothesis. Conversely, minimal non-realizable samples of growing size can be planted in distributions so that every proper learner pays the logarithmic factor.

## Depends on

- [Dual Helly number of a concept class](dual-helly-number.md)

## Proof depends on

- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)
- [Bagging with logarithmically many bootstrap samples is an optimal PAC learner](bagging-optimal-pac-learner.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
- S. Hanneke, "The Optimal Sample Complexity of PAC Learning", Journal of Machine Learning Research 17 (2016), arXiv:1507.00473.
