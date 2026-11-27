# Bagging with logarithmically many bootstrap samples is an optimal PAC learner

Let $H \subseteq \{0,1\}^X$ have VC dimension $d$. Consider the learner that draws $T = O(\log(n/\delta))$ bootstrap samples of size $n$ (sampling with replacement from the training sample $S$ of size $n$), runs an arbitrary empirical risk minimizer for $H$ on each, and outputs the majority vote. Then for every realizable $D$, with probability at least $1-\delta$ over $S$ and the bootstrap draws,

$$
\mathrm{er}_D(\hat h) = O\!\left(\frac{d + \log(1/\delta)}{n}\right),
$$

matching the lower bound for all PAC learners. In contrast, an individual empirical risk minimizer can incur an extra $\log(1/\varepsilon)$ factor.

## Proof sketch

Following Hanneke's analysis of recursive subsample majorities, it suffices to show that for every fixed test point the fraction of voters that err is below one half except on a set of small probability mass. Bootstrap samples are approximately as diverse as Hanneke's structured subsamples: a point is misclassified by the majority only if a constant fraction of bootstrap ERMs err there, and the region where a single ERM errs has mass $O((d + \log(1/\delta))/n)$ after a uniform convergence argument on the region of disagreement. A union bound over $O(\log(n/\delta))$ voters completes the bound.

## Depends on

- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)
- [Fundamental theorem of statistical learning (binary, 0-1 loss)](../../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/fundamental-theorem-of-statistical-learning.md)
- [Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners](leave-one-out-to-high-probability.md)

## Sources

- K. G. Larsen, "Bagging is an Optimal PAC Learner", COLT (2023), arXiv:2212.02264.
- S. Hanneke, "The Optimal Sample Complexity of PAC Learning", Journal of Machine Learning Research 17 (2016), arXiv:1507.00473.
