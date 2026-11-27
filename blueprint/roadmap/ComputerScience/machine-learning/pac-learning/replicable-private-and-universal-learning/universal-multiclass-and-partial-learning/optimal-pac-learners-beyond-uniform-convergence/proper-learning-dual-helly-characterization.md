# Proper learners attain the optimal PAC rate exactly when the dual Helly number is bounded

If the dual Helly number $k_w$ of $H$ is finite, there exists a proper learner for $H$ (one that always outputs a concept of $H$) with sample complexity $O\big(\tfrac{k^2}{\varepsilon}\,(d \log k + \log(1/\delta))\big)$ for VC dimension $d$, where $k \le k_w$ is the projection number of $H$; for fixed $k_w$ this is $O\big((d + \log(1/\delta))/\varepsilon\big)$. Conversely, if the hollow star number of $H$ is infinite, then the proper sample complexity is not $o\big(\tfrac{1}{\varepsilon}\log\tfrac{1}{\varepsilon}\big)$: there are $\varepsilon_i \to 0$ with proper sample complexity at least $\tfrac{c}{\varepsilon_i}\log\tfrac{1}{\varepsilon_i}$ at fixed $\delta$. For a closed class (every set of labelled examples consistent with no concept of $H$ has a finite subset consistent with no concept of $H$) the hollow star, projection and dual Helly numbers coincide, so an infinite dual Helly number forces this extra logarithmic factor. So for closed classes a proper learner attains the optimal rate if and only if the dual Helly number is finite.

## Proof sketch

The projection number $k_p \le k_w$ is the least $k$ such that for every finite multiset $C' \subseteq H$ some concept of $H$ agrees with the majority vote of $C'$ on all points where that vote is backed in the required sense by $k$-subsets. The proper learner takes Hanneke's majority vote of ERMs on recursively constructed subsamples and projects it to such a concept; the improper analysis transfers at the cost of the factor $k_p^2$. Conversely, large hollow star sets can be planted in distributions, in the manner of Daniely and Shalev-Shwartz, so that every proper learner pays the logarithmic factor.

## Depends on

- [Dual Helly number of a concept class](dual-helly-number.md)

## Proof depends on

- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818, Definitions 2–4, Lemma 5, Theorems 8 and 10.
- S. Hanneke, "The Optimal Sample Complexity of PAC Learning", Journal of Machine Learning Research 17 (2016), arXiv:1507.00473.
